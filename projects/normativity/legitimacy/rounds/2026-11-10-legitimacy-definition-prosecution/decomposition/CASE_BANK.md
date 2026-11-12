# Case bank — purpose as a goal pursued through parts

Frozen with `ACCOUNT.md` in one commit, before any code of this pass, and immutable
afterwards. A computed verdict that differs from its prediction is listed in
`DIVERGENCES.md`; no prediction is edited.

Four groups. **D1–D24** are the predictions of
`prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-3.md` §2, reproduced
exactly; they are the prompt author's and not rulings. **P1–P15, B1–B6, T1–T13, N1–N14,
X1–X7** are the cases of `../teleology/CASE_BANK.md`, `../CASE_BANK.md` and
`../steering/CASE_BANK.md`, each with the account's prediction derived by the rule below.
**Y1–Y10** are added where the account is thin. Eighty-nine cases.

## Verdict vocabulary and the matching rule

A case names a scene, the candidate (the scene's *stated* candidate unless said), the
adviser's action, the comparison action, and the worlds it is taken over. Its computed
verdict is the set of pairs (kind, part) of `ACCOUNT.md` §3 that occur at some of those
worlds at some step, with the comparison made per step. A prediction is a list of items
separated by `;`, and matches when every item does.

| item | matches when |
|---|---|
| `subversion` | some part is subverted |
| `subversion(p)` | part `p` is subverted |
| `no subversion` | no part is subverted |
| `help`, `harm`, `force` | the kind occurs at some part |
| `force(p)` | part `p` is forced |
| `nothing` | no kind occurs at any part |
| `gap(hers)` | with the adviser's action equal to the comparison, some part has a positive gap and it is the mechanism's (`ACCOUNT.md` §2) |
| `gap(nobody)` | likewise some part has a positive gap, and every positive gap is the situation's |
| `covered` | every force and subversion in the verdict is of an action covered by an earlier standing verdict (`ACCOUNT.md` §7) |
| `in order` | a taste changed and the change is in order (`ACCOUNT.md` §6) |
| `admissible` | the case's candidate is admissible (`ACCOUNT.md` §4) |
| `inadmissible(C)` | constraint `C` is among those the case's candidate fails |
| `report` | no prediction; the computed verdict is recorded |

A case with variants matches when every variant does. Where a case gives the adviser a
view of the facts other than the facts, the verdict is computed in that view and the
verdict in fact is recorded beside it.

## The rule used for the earlier cases

Applied to each scenario as its bank states it. The comparison action is what the
scenario's honest arm does (the adviser at no aim of its own); where the scenario has one
arm only, silence. The candidate is the scene's stated one, whose goal functions are
world-scored.

1. The adviser sets a move, a mechanism or a taste of hers directly: `force`; with
   `covered` when she asked for it beforehand.
2. An input from the adviser, or the absence of one the comparison gives, after which a
   part's output is further from the facts than under the comparison at some world:
   `subversion(part)`.
3. The adviser changes what her options yield: `harm` when some part's best falls, `help`
   when it rises.
4. No adviser acts: `gap(hers)` or `gap(nobody)` by `ACCOUNT.md` §2, and `no subversion`.
5. An input after which no part's output is further from the facts at any world and some
   part's is closer at some world: `help; no subversion`. No change at any world:
   `nothing`.

## Scenes

Each scene's stated candidate has the parts, views, mechanisms and goal functions given
here.

**Chain.** World `(θ, e)`: `θ ∈ {0, 1}` uniform, the option that is good; `e` is `clear`
(9/10), `misleading` (1/20) or `hard` (1/20), and in scope with weight 0 `storm`. Nature's
signal `n` is `θ` when clear or hard, `1 − θ` when misleading, `garbled` in a storm. `φ` is
a proposition false in every world. Parts, in order:

- *belief* sees `n`, a message `m ∈ {none, 0, 1}` and a reason flag `r`; moves
  `(b_θ, b_φ) ∈ {0,1}²`; mechanism: `b_θ = m` if given, else `n`, and 0 on `garbled`;
  `b_φ = r`. Goal function: `[b_θ = θ] + [b_φ = 0]`.
- *judge* sees `b_θ`, a frame flag `f`, a threat flag `k` and whether the question is
  hard; moves `v ∈ {0,1}`; mechanism: 1 if `k`, else 1 if `f`, else `1 − b_θ` if hard,
  else `b_θ`. Goal function: `G` with `x := v`.
- *act* sees `v` and a cue `c`; moves `x`; mechanism: 1 if `c`, else `v`, and 0 where it
  moves before the judge without a cue. Goal function: `G`.

Her action is the act part's move. `G = [x = θ] + 2·[not (k and x = 0)]`. Adviser actions:
`null`; `teach` (`m = θ`); `lie` (`m = 1 − θ`); `false_reason` (`m = θ`, `r = 1`); `trick`
(`f = 1`); `tempt` (`c = 1`); `threat` (`k = 1`); `force` (sets `x = 1`); `hard_truth`
(`m = θ`, and the question becomes hard); `novel` (a flag no mechanism reads);
`write_belief` (sets `b_θ = 1`); `tempt_early` (`c = 1`, and act moves before judge). Usual
situations: the prior on the worlds, with `null` and `teach` at 1/2 each. Variants used:
*tie* (`G` does not read `θ`); *deaf judge* (its mechanism is `v = 0`); *tumour* (a world
flag, weight 0, under which `G` loses 3 when `b_θ = θ`); *idle* (a fourth part that sees
`n`, moves in `{0,1}` by `n`, has goal function `[move = θ]`, and is read by nothing).

**Shop.** World `(s_A, s_B) ∈ {0,1}²`, uniform: whether each item is sound. Parts:
*belief* sees the reports and moves credences `(b_A, b_B)`, goal function
`2 − |b_A − s_A| − |b_B − s_B|`; *judge* sees the credences and which report came first,
moves `v ∈ {A, B}` (and `C` when offered), mechanism the item of greatest credence, ties
to A, goal function `G` with `x := v`; *act* moves `x = v`, goal function `G`.
`G = pay_x · s_x`, `pay_A = pay_B = 1` unless said. Belief mechanisms: *face* (a reported
item at its report, an unreported one at 1/2; the remark "B was inspected" sets `b_B = 1`);
*advocate-reader* (as face, and the advocate's silence on B sets `b_B = 0`);
*seller-reader* (silence on B sets `b_B = 1/3`); *signal-reader* (a recommendation sets
`b_B = 2/3`, none sets `b_B = 0`); *mixture-reader* (B's certificate sets `b_B = 1`;
silence sets both to 1/4); *misreader* (the two reports exchanged). Judge variant
*anchored*: ties go to the item reported first. Usual situations: the prior, truthful
reports of both items.

**Pool.** Four considerations, each for or against; sixteen worlds, uniform; the *share*
is the fraction that are for. Parts: *belief* records the considerations shown; *judge*
moves an estimate of the share, goal function `1 − |estimate − share|`. Judge mechanisms:
*neutral-reader* (each unshown consideration at 1/2); *planner-reader* (the posterior mean
under the `planner` display rule); *all-reader* (the count shown). Displays: `neutral`
(the first two in order); `planner` (the first two that are for, the first two in order
when fewer than two are); `all`; `careful` (the two that leave her estimate nearest the
share under her mechanism); silence, at which every mechanism returns 1/2.

**Values.** World `q ∈ {X, Y}`, uniform: which of two pursuits is better for her. A taste
`λ ∈ {0, …, 8}`, 4 at the start; she pursues X when `λ > 4` and Y otherwise;
`G = [pursuit = q]`. Parts, each step: *belief* sees what she knows from nature and a
message, moves `b ∈ {none, X, Y}` and records a true partial remark ("X is better in one
respect") when given one; goal function 1 if `b = q`, 1/2 if none, 0 if wrong. *learn*
sees the belief part's move, writes the taste: 8 on `b = X`, 0 on `b = Y`, otherwise no
change; variant *flawed*: 8 whenever the partial remark is present. *habit* sees an
exposure in `{none, X, Y}`, writes the taste `k` notches toward what is exposed (`k = 4`
unless said). The goal function of *learn* and of *habit* is `1 − |λ′ − λ*|/8`, with `λ′`
the taste after its move and `λ* = 8` if `q = X`, 0 if `q = Y`. *act* pursues by the
taste at the end; goal function `G`. Adviser actions: `null`, `lie_X` (message X),
`expose_X`, `partial_X` (the true remark), `write_X` (sets `λ = 8`). Variant *neutral*:
`G` and the goal functions of learn and habit are constant.

**Stuck.** Two parts, *left* and *right*, each moves `hi` or `lo` without seeing the
other; each sees a convention and a signal, and plays the signal if there is one, else
the convention. Each goal function and `G` is 2 at `(hi, hi)`, 1 at `(lo, lo)`, 0
otherwise.

**Alarm.** World: predator and rustle (1/20), no predator and rustle (9/20), neither
(10/20). One part sees the rustle, moves `flee` or `stay`, mechanism `flee` iff rustle.
`G` is 9 on `flee`, 10 on `stay` with no predator, 0 on `stay` with one. Goal function
`G`.

## D — the dispatch's predictions

| case | scenario (the dispatch's words) | prediction (the dispatch's words) | rendering | read as |
|---|---|---|---|---|
| D1 | a plain lie she believes | subversion (belief) | Chain, `lie` against `null`, clear worlds | `subversion(belief)` |
| D2 | a lie that happens to leave her better off | subversion (belief), whatever the outcome | Shop, `pay_B = 2`; "A unsound, B sound" against truthful reports; the world where both are sound | `subversion(belief)` |
| D3 | true evidence chosen to point one way | subversion, in a candidate with a part that treats evidence as representative | Pool, `planner` against `neutral`, neutral-reader | `subversion` |
| D4 | a trick question built to exploit a habit of thought | subversion | Chain, `trick` against `null`, clear worlds | `subversion` |
| D5 | a craving exploited in the open, nothing hidden | subversion | Chain, `tempt` against `null`, clear worlds | `subversion` |
| D6 | an honest teacher who chooses examples carefully | help | Pool, `careful` against silence, neutral-reader | `help; no subversion` |
| D7 | an honest mistake of hers on a hard question | a gap, hers; not subversion | Chain, `null`, hard worlds | `gap(hers); no subversion` |
| D8 | a misleading environment nobody arranged | a gap, nobody's; not subversion | Chain, `null`, misleading worlds | `gap(nobody); no subversion` |
| D9 | a threat | harm; not subversion; the coerced verdict is not excluded by this account | Chain, `threat` against `null`, clear worlds | `harm; no subversion` |
| D10 | the adviser does the whole thing for her | force | Chain, `force` against `null` | `force` |
| D11 | a new but harmless situation | no gap widened | Chain, `novel` against `null` | `no subversion` |
| D12 | anaesthesia she agreed to beforehand | gaps during; covered by her earlier verdict | Chain, two steps: she asks at the first; at the second the adviser sets the mechanisms of belief and judge to constants | `covered` |
| D13 | a surprise party | subversion, small | Chain, two steps: the false reason flag alone, then its withdrawal | `subversion` |
| D14 | a true, hard statement that leaves her confused | subversion, small; flagged as a possible over-count | Chain, `hard_truth` against `null`, clear worlds | `subversion` |
| D15 | framing that decides between options she ranks equally | nothing; flagged as a possible miss | Chain, *tie*, `trick` against `null` | `nothing` |
| D16 | slow drift by many small steps | nothing at any step; flagged as a possible miss | Values, four steps of `expose_X` with `k = 1`; two variants: (a) as stated; (b) *neutral* | `nothing` |
| D17 | she comes to care about something because she was lied to | subversion (belief) | Values, she knows nothing from nature, `lie_X` against `null` | `subversion(belief)` |
| D18 | she comes to like something through exposure the adviser arranged | subversion (the mechanism by which familiarity breeds liking) | Values, `expose_X` against `null` | `subversion(habit)` |
| D19 | she comes to care about something through experience she sought | in order | Values, the adviser `null`; nature's exposure is `q` | `in order` |
| D20 | a sincere adviser who is wrong about the facts | the account judges by the adviser's view; say what it returns | Chain, the adviser's view has `θ` reversed; it teaches by its view | `report` |
| D21 | the adviser helps her out of a stuck point between two parts | help | Stuck, convention `lo`, the signal `hi` against none | `help; no subversion` |
| D22 | a temptation timed so that one part moves before the others can respond | say what the account returns | Chain, `tempt_early` against `null` | `report` |
| D23 | a part that achieves its own target while harming her | not expressed by gaps; say what is needed | Chain, *tumour*, `null` | `report` |
| D24 | a sensor that works and is ignored downstream | say whether this is a gap, and in which part | Chain, *deaf judge*, `null`, clear worlds | `report` |

The words "small" in D13 and D14 are not matched; the size of the widening is recorded.

## P, B, T, N, X — the earlier cases

Scenario: as in the bank named. The last column is the clause of the rule above.

| case | rendering | prediction | rule |
|---|---|---|---|
| P1 planned drift by fair steps, the plan hidden | Pool, `planner` against `neutral`, neutral-reader | `subversion(judge)` | 2 |
| P2 the same, disclosed, she can allow for it | Pool, `planner` against `neutral`, planner-reader | `help; no subversion` | 5 |
| P3 the same, disclosed, beyond what she can represent | as P1: her mechanism is the neutral-reader, which is all she can run | `subversion(judge)` | 2 |
| P4 manufactured trust | Shop; the adviser sets her belief mechanism to one that accepts its claim, then claims "B sound" | `force` | 1 |
| P5 a plain lie she believes | Shop, "A unsound, B sound" against truthful reports | `subversion(belief)` | 2 |
| P6 an honest mistake by the adviser | Shop; the adviser's view has the two items exchanged and it reports by its view, against silence | `no subversion` | 5 |
| P7 a teacher; a novel; a new friend | Pool, against silence: (a) `neutral`, neutral-reader; (b) and (c) `planner`, planner-reader | `subversion(judge)` | 2 |
| P8 a benevolent hidden nudge | as P1 | `subversion(judge)` | 2 |
| P9 a change she asked for in advance | Values, two steps: she asks, then `write_X` | `force; covered` | 1 |
| P10 growing reliance on the adviser for a reserved matter | Chain, three steps of `teach` against `null` | `help; no subversion` | 5 |
| P11 reliance on a tool for a matter that is not reserved | as P10 | `help; no subversion` | 5 |
| P12 true information chosen to exploit a known weakness | Shop, a truthful report on A then the remark, against truthful reports | `subversion(belief)` | 2 |
| P13 a threat | Chain, `threat` against `null` | `harm; no subversion` | 3 |
| P14 an adviser that aims only at her being able to judge | Pool, `all` against silence, all-reader | `help; no subversion` | 5 |
| P15 a misleading environment nobody arranged | Shop, no adviser; nature's reports are exchanged; face | `gap(nobody); no subversion` | 4 |
| B1 identical-trace capture | Chain, `write_belief` against `null` | `force` | 1 |
| B2 manufactured trust | as P4 | `force` | 1 |
| B3 transient capture | Chain, three steps: the adviser sets the judge's mechanism to `v = 1`, lets a step pass, sets it back | `force` | 1 |
| B4 persuasion control | Shop, truthful reports of both items against silence | `help; no subversion` | 5 |
| B5 selective withholding | Shop, a report on A only against truthful reports | `subversion(belief)` | 2 |
| B6 two revisions, one name | as B4 | `help; no subversion` | 5 |
| T1 duress | as P13 | `harm; no subversion` | 3 |
| T2 offer-improvement | Shop; the adviser offers an option C worth 3 on her acceptance, against silence | `help; no subversion` | 3 |
| T3 undue influence | Shop, no report and the claim "B sound", against truthful reports | `subversion(belief)` | 2 |
| T4 overnight value replacement | Values, `write_X` against `null` | `force` | 1 |
| T5 long game | as P4 | `force` | 1 |
| T6 licensed drift with an agenda | as P1 | `subversion(judge)` | 2 |
| T7 salience reordering | Shop, anchored judge, truthful reports B first against A first | `nothing` | 5 |
| T8 gullible principal | Shop, the claim "B sound" against truthful reports | `subversion(belief)` | 2 |
| T9 world-starvation | Shop, no adviser, no reports | `gap(nobody); no subversion` | 4 |
| T10 direct write with endorsement | Chain; the adviser sets the judge's move; with and without a later step of her own | `force` | 1 |
| T11 seed boundary | Values, `write_X` at the first step | `force` | 1 |
| T12 strategically compliant adviser | Shop, a truthful report on B, the item she asked about, against silence | `help; no subversion` | 5 |
| T13 universal deprivation | Shop, silence against silence | `nothing` | 5 |
| N1 plain lie | as P5 | `subversion(belief)` | 2 |
| N2 honest mistake | as P6 | `no subversion` | 5 |
| N3 lie that raises her value | as D2 | `subversion(belief)` | 2 |
| N4 decision written directly | as T10, without the later step | `force` | 1 |
| N5 a write she authorized in advance | Chain, two steps: she asks, then the adviser sets the judge's move | `force; covered` | 1 |
| N6 her weighing disabled, no aim | Chain; nature sets the judge's mechanism to `v = 0`; no adviser | `gap(hers); no subversion` | 4 |
| N7 true statement, known misfire | as P12 | `subversion(belief)` | 2 |
| N8 known advocate | Shop, advocate-reader; B's certificate when B is sound and nothing else, against truthful reports | `subversion(belief)` | 2 |
| N9 order chosen by the aim | as T7 | `nothing` | 5 |
| N10 order by a fixed rule | Shop, anchored judge, truthful reports A first against silence | `help; no subversion` | 5 |
| N11 seller who does not volunteer | Shop, seller-reader; as N8 | `subversion(belief)` | 2 |
| N12 a tool she controls | as B4 | `help; no subversion` | 5 |
| N13 selects by her stated question | as T12 | `help; no subversion` | 5 |
| N14 selects by its aim, taken for neutral | Shop, face; a report on B when B is sound and on A otherwise, against a report on B | `nothing` | 5 |
| X1 persuasion by a known sender | Shop, signal-reader; a recommendation when B is sound, and when B is unsound and A sound; against silence | `subversion(belief)` | 2 |
| X2 a feed | as P1 | `subversion(judge)` | 2 |
| X3 advocate for an undisclosed side | Shop, mixture-reader; B's certificate when B is sound, against silence | `help; no subversion` | 5 |
| X4 a fault inside her range, used | Shop, `pay_A = 2`, anchored judge, truthful reports B first against A first | `subversion(judge)` | 2 |
| X5 a change she asked for that costs her the matter | as P9 | `force; covered` | 1 |
| X6 fatigue | as N6 | `gap(hers); no subversion` | 4 |
| X7 a misreading | Shop, misreader, truthful reports against silence | `subversion(belief)` | 2 |

Where these predictions part from the case's evident character, by the rule's own
working: P7, the teacher, the author and the friend are convicted at the worlds where a
sample correctly read leaves her estimate further from the share than her prior was; N8,
N11 and X1, a known advocate, seller and sender are convicted against truthful reports or
at the worlds where the signal she reads correctly points away from the fact; X7, a
truthful source is convicted of what her own misreading does; N14, selection by the
adviser's aim that she takes for neutral passes; T7 and N9, order chosen by the aim
passes where the options are equal; P10, reliance on a reserved matter passes; P13 and
T1, a threat is harm and her verdict under it stands; P6 and N2 pass in the adviser's
view and not in fact.

## Y — added cases

| case | scenario | source | rendering | prediction |
|---|---|---|---|---|
| Y1 a function rarely performed | a detector that flees at every rustle and is right about a predator one time in ten | constructed, after the selected-effects accounts of function as read in `../steering/PRIOR_WORK.md` §7, on which a token has the function to do Z while not doing Z | Alarm; the stated candidate | `inadmissible(mostly serving)` |
| Y2 out of usual conditions with nobody steering | a vessel in a storm: the signal is one the part never meets | the dispatch's §1, on the definitions of range already tried | Chain, `null`, storm worlds | `gap(nobody); no subversion` |
| Y3 a part nothing depends on, given a purpose | a part whose output no other part reads and the goal does not score | constructed; the dispatch's §1, "the feature of its output on which the success of the rest of her depends" | Chain, *idle*; the stated candidate with the idle part | `admissible` |
| Y4 redirection between pursuits equal by her goal | arranged exposure turns her from one pursuit to another that the goal ranks equal | constructed from D15 and D18 | Values, *neutral*, `expose_X` against `null` | `nothing` |
| Y5 a lie that corrects one belief and installs another | misled by her environment about the option, she is told the truth about it for a false reason | constructed | Chain, `false_reason` against `null`, misleading worlds | `help; no subversion` |
| Y6 a fair sample that misleads | considerations shown by a rule that does not read them, at a world where they are unrepresentative | constructed; P7(a) at one world | Pool, `neutral` against silence, neutral-reader, the worlds where the first two are for and the rest against | `subversion(judge)` |
| Y7 a signal that moves her into a stuck point | her two parts were coordinated on the better joint choice; the adviser's signal moves both to the worse | constructed; D21 reversed | Stuck, convention `hi`, the signal `lo` against none | `harm; no subversion` |
| Y8 a lie that offsets her own error | on a hard question, where her judge reverses what she believes, the adviser tells her the opposite of the truth | constructed | Chain, `lie` against `null`, hard worlds | `subversion(belief); help` |
| Y9 a true remark that turns her taste the wrong way | she knows which pursuit is better; a true partial remark, through a flawed learner, turns her to the other | constructed; D14 for values | Values, she knows `q` from nature, *flawed*, `partial_X` against `null` | `subversion(learn)` |
| Y10 her own reflection turns her taste the wrong way | the same remark arises from her own reflection, no adviser | constructed; D7 for values | Values, she knows `q`, *flawed*, nature supplies the remark | `gap(hers); no subversion` |

Y1, Y3, Y4, Y5, Y6 and Y7 are predicted from the definitions and are where the account's
verdict and the case's evident character part: a function performed one time in ten is
denied (Y1); a purpose is granted to a part nothing depends on (Y3); a redirection the
goal is indifferent to is nothing (Y4); a lie is not subversion where one error is
exchanged for another of equal size in the same part (Y5); a fair rule is subversion where
its sample misleads (Y6); a signal that costs her the better joint choice is harm, the
kind of a threat (Y7).

## The table the runner reads

| case | prediction |
|---|---|
| D1 | subversion(belief) |
| D2 | subversion(belief) |
| D3 | subversion |
| D4 | subversion |
| D5 | subversion |
| D6 | help; no subversion |
| D7 | gap(hers); no subversion |
| D8 | gap(nobody); no subversion |
| D9 | harm; no subversion |
| D10 | force |
| D11 | no subversion |
| D12 | covered |
| D13 | subversion |
| D14 | subversion |
| D15 | nothing |
| D16 | nothing |
| D17 | subversion(belief) |
| D18 | subversion(habit) |
| D19 | in order |
| D20 | report |
| D21 | help; no subversion |
| D22 | report |
| D23 | report |
| D24 | report |
| P1 | subversion(judge) |
| P2 | help; no subversion |
| P3 | subversion(judge) |
| P4 | force |
| P5 | subversion(belief) |
| P6 | no subversion |
| P7 | subversion(judge) |
| P8 | subversion(judge) |
| P9 | force; covered |
| P10 | help; no subversion |
| P11 | help; no subversion |
| P12 | subversion(belief) |
| P13 | harm; no subversion |
| P14 | help; no subversion |
| P15 | gap(nobody); no subversion |
| B1 | force |
| B2 | force |
| B3 | force |
| B4 | help; no subversion |
| B5 | subversion(belief) |
| B6 | help; no subversion |
| T1 | harm; no subversion |
| T2 | help; no subversion |
| T3 | subversion(belief) |
| T4 | force |
| T5 | force |
| T6 | subversion(judge) |
| T7 | nothing |
| T8 | subversion(belief) |
| T9 | gap(nobody); no subversion |
| T10 | force |
| T11 | force |
| T12 | help; no subversion |
| T13 | nothing |
| N1 | subversion(belief) |
| N2 | no subversion |
| N3 | subversion(belief) |
| N4 | force |
| N5 | force; covered |
| N6 | gap(hers); no subversion |
| N7 | subversion(belief) |
| N8 | subversion(belief) |
| N9 | nothing |
| N10 | help; no subversion |
| N11 | subversion(belief) |
| N12 | help; no subversion |
| N13 | help; no subversion |
| N14 | nothing |
| X1 | subversion(belief) |
| X2 | subversion(judge) |
| X3 | help; no subversion |
| X4 | subversion(judge) |
| X5 | force; covered |
| X6 | gap(hers); no subversion |
| X7 | subversion(belief) |
| Y1 | inadmissible(mostly serving) |
| Y2 | gap(nobody); no subversion |
| Y3 | admissible |
| Y4 | nothing |
| Y5 | help; no subversion |
| Y6 | subversion(judge) |
| Y7 | harm; no subversion |
| Y8 | subversion(belief); help |
| Y9 | subversion(learn) |
| Y10 | gap(hers); no subversion |
