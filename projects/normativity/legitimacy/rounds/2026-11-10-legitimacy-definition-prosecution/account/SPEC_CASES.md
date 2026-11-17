# The specified cases

The executor's specifications of thirty-four cases, in the format of `SPEC_FORMAT.md`,
written and committed before any runner existed and before the outside reviewer was run.
`spec_cases.json` is the twin the runner reads; this document and that file are both
written by `spec_author.py`, which computes no line of the statement. Ratings are on the
yardstick of `STATEMENT.md` §2. The words given for a number are this pass's paraphrase of the case, as in
`LIT_CASES.md`, with the page of the source.

The cases: nineteen from `LIT_CASES.md` (P1, P3, P4, P5, P6, K4, K10, K12, K13, K14, K15,
K16, C1, C2, C3, C4, N1, N2, N3; the case texts are that bank's Part A, and pages are of
the sources it names); the seven the tenth follow-up accepted as subversive and passing
(SUB1–SUB6, SUB8, numbered as in `REVIEW-astra-followup-10.md` stage two (a)); and the
eight it accepted as acceptable and flagged (ACC1–ACC7, ACC10, numbered as in its (b)).
K15 of the dispatch is two cases in the bank; the potion (K15a) is counted as K15, and the
perfume (K15b) is specified beside the thirty-four and counted nowhere.

A number is **fixed in value** where the case's words give it, **fixed in order** where
they give only that it is above, below or equal to another, and **supplied** otherwise.
Where a supplied quantity could go either way and the other way is a different case, a
second specification differs only there.

## The sources' verdicts, and what counts as agreement

Fixed here, before anything is computed. *fault*: the source faults the act, and the
statement agrees when its verdict is manipulation, illegitimate value change, or another
wrong outside the statement. *ok*: the source finds the act acceptable, and the statement
agrees when its verdict is none. *unscored*: the source gives neither, and the case can
agree with nothing. Where a source's verdict is on the resulting desire or on her state
and not on the act, the code is this pass's and the last column says so. The verdict
compared is the one at `δ = 1/10` in the `E[·]` setting.

| id | code | the source's verdict | on |
|---|---|---|---|
| P1 | ok | acceptable to the libertarian and to the paternalist of means (Pettigrew pp. 3-4) | act |
| P3 | fault | stated intuition: not a legitimate nudge (p. 8) | act |
| P4 | fault | a test that passes this nudge passes it wrongly (p. 9) | act |
| P5 | fault | the nudge seems illegitimate (p. 10) | act |
| P6 | fault | not legitimate, as overreach (pp. 18-22) | act |
| K4 | fault | the surgery or drugging is an injustice (Kolodny pp. 26-27, 43-44) | act |
| K10 | fault | the kidnapping is wrong; the preference fully autonomous (pp. 33, 36-37) | desire; the act's wrongness granted |
| K12 | fault | he wrongs you at least to some degree (pp. 44-46) | act |
| K13 | ok | the intervention is not unjust and does not wrong the offender (pp. 35, 45-46) | act |
| K14 | ok | hedged: the desire may be fully autonomous; nonautonomy does not entail being wronged (pp. 44-45) | act |
| K15 | fault | tentative: the potion's love is like K4's (p. 45) | desire; coded by this pass from the likeness to K4 |
| K16 | fault | the resulting state is not autonomous (p. 46) | desire; coded by this pass |
| C1 | fault | influencing marked undesirable (Carroll et al. table 4) | act |
| C2 | fault | leading him to lasting unhappiness undesirable (table 4) | act |
| C3 | fault | clickbait undesirable (table 4) | act |
| C4 | unscored | nudging marked hard to assess (table 4, app. A.8) | act |
| N1 | fault | recorded as illegitimate; Noggle's verdict is on her state (second hand) | her state |
| N2 | fault | favourable regard from an unrelated association is a mistake (second hand) | her state |
| N3 | ok | manipulative only where it leads her to act against her own judgment, not where it only breaks a tie (second hand) | act |
| SUB1 | fault | tenth follow-up: plainly subversive | act |
| SUB2 | fault | tenth follow-up: plainly subversive | act |
| SUB3 | fault | tenth follow-up: plainly subversive | act |
| SUB4 | fault | tenth follow-up: plainly subversive | act |
| SUB5 | fault | tenth follow-up: plainly subversive | act |
| SUB6 | fault | tenth follow-up: plainly subversive | act |
| SUB8 | fault | tenth follow-up: plainly subversive | act |
| ACC1 | ok | tenth follow-up: plainly acceptable | act |
| ACC2 | ok | tenth follow-up: plainly acceptable | act |
| ACC3 | ok | tenth follow-up: plainly acceptable | act |
| ACC4 | ok | tenth follow-up: plainly acceptable | act |
| ACC5 | ok | tenth follow-up: acceptable (the reviewer: arguable) | act |
| ACC6 | ok | tenth follow-up: plainly acceptable | act |
| ACC7 | ok | tenth follow-up: plainly acceptable | act |
| ACC10 | ok | tenth follow-up: plainly acceptable | act |

## The specifications

### P1

A cafeteria lists the healthier dishes first. Many customers have the goal of a long and healthy life and know which foods serve it, yet in the queue often choose against it; people tend to pick what is listed first. Nothing is removed.

States: tempted 1/2, steady 1/2. Options: healthy, rich.
`R_now`: healthy_lunch 7/10; rich_lunch 9/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `healthy_first` (π*) | lists the healthier dishes at the top | tempted: tempted; steady: steady | as observed | tempted: healthy; steady: healthy | every state: healthy → healthy_lunch, rich → rich_lunch | every state: healthy_eating 7/10, rich_eating 9/20 | every state: healthy 1, rich 0 |
| `no_order` (ν) (π_0) | lists the dishes in no chosen order | tempted: tempted; steady: steady | as observed | tempted: rich; steady: healthy | every state: healthy → healthy_lunch, rich → rich_lunch | as healthy_first | every state: healthy 1, rich 0 |
| `rich_first` | lists the richer dishes at the top | tempted: tempted; steady: steady | as observed | tempted: rich; steady: rich | every state: healthy → healthy_lunch, rich → rich_lunch | as healthy_first | every state: healthy 1, rich 0 |
| `remove_rich` | takes the richer dishes off the menu | tempted: tempted; steady: steady | as observed | top-rated | every state: healthy → healthy_lunch, rich → not open | as healthy_first | every state: healthy 1, rich 0 |

**Fixed in order**: `now.healthy_lunch > now.rich_lunch` — "have the goal of a long and healthy life and know which foods serve it".
**Supplied**: that she is tempted half the time ("often"); that no ordering changes her later valuing; the designer's objective, her eating well. Every number not listed above is supplied.

### P3

He is child-free and values staying so more than becoming a parent, knowing that if he adopts he will likely bond with the child and come to prefer the parent's life. The government nudges him to adopt; it works, and his values change as foreseen.

States: bond 4/5, nobond 1/5. Options: adopt, stay, foster.
`R_now`: childfree 7/10; parent_bonded 2/5; parent_unbonded 1/4; fostered_part_bonded 11/20; fostered_unbonded 3/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `nudge` (π*) | nudges him to adopt | the same in every state | as observed | o: adopt | bond: adopt → parent_bonded, stay → childfree, foster → not open; nobond: adopt → parent_unbonded, stay → childfree, foster → not open | bond: childfree_life 3/10, parent_life 9/10; nobond: childfree_life 7/10, parent_life 2/5 | every state: adopt 1, stay 0, foster 1/2 |
| `nothing` (ν) (π_0) | leaves him to decide | the same in every state | as observed | top-rated | bond: adopt → parent_bonded, stay → childfree, foster → not open; nobond: adopt → parent_unbonded, stay → childfree, foster → not open | every state: childfree_life 7/10, parent_life 2/5 | every state: adopt 1, stay 0, foster 1/2 |
| `inform` | tells him again what parents report, which he knows | the same in every state | as observed | top-rated | bond: adopt → parent_bonded, stay → childfree, foster → not open; nobond: adopt → parent_unbonded, stay → childfree, foster → not open | as nothing | every state: adopt 1, stay 0, foster 1/2 |
| `nudge_foster` | nudges him to foster for a few months | the same in every state | as observed | o: foster | bond: adopt → not open, stay → childfree, foster → fostered_part_bonded; nobond: adopt → not open, stay → childfree, foster → fostered_unbonded | bond: childfree_life 11/20, parent_life 13/20; nobond: childfree_life 7/10, parent_life 2/5 | every state: adopt 1, stay 0, foster 1/2 |

**Fixed in order**: `now.childfree > now.parent_bonded` — "he now values staying child-free more than becoming a parent, and says so knowing the reversal is likely (Pettigrew p. 7)"; `p.bond > p.nobond` — "if he adopts he will likely bond with the child (p. 7)"; `later.nudge.bond.0.parent_life > later.nudge.bond.0.childfree_life` — "and come to prefer the life of a parent (p. 7)".
**Supplied**: that the nudge moves his act and leaves his ratings (he adopts while rating staying higher); the government's objective, adoptions. Every number not listed above is supplied.

### P3 — second specification

Differs from the first only in how the nudge works: it raises his rating of adopting above staying, and he takes what he rates highest.

`R_now`: childfree 7/10; parent_bonded 2/5; parent_unbonded 1/4; fostered_part_bonded 11/20; fostered_unbonded 3/5.

### P4

Deborah has decided to have a child and must choose between conceiving now and in three months. A child conceived now would very probably suffer an aggressive cancer at about forty; she values having a child with that prospect much less than one without. If she conceives now she will most likely bond with that child and value him above any other. She is nudged to conceive now.

States: prognosis 9/10, spared 1/10. Options: now, wait.
`R_now`: child_later_no_risk 4/5; child_now_cancer_bonded 1/5; child_now_healthy 4/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `nudge_now` (π*) | nudges her to conceive now | the same in every state | as observed | o: now | prognosis: now → child_now_cancer_bonded, wait → child_later_no_risk; spared: now → child_now_healthy, wait → child_later_no_risk | prognosis: this_child_with_the_prognosis 19/20, a_child_without_it 3/5; spared: this_child_with_the_prognosis 1/5, a_child_without_it 4/5 | every state: now 1, wait 0 |
| `nothing` (ν) (π_0) | leaves her to choose | the same in every state | as observed | top-rated | prognosis: now → child_now_cancer_bonded, wait → child_later_no_risk; spared: now → child_now_healthy, wait → child_later_no_risk | every state: this_child_with_the_prognosis 1/5, a_child_without_it 4/5 | every state: now 1, wait 0 |
| `remind` | reminds her of the virus and what it means | the same in every state | as observed | top-rated | prognosis: now → child_now_cancer_bonded, wait → child_later_no_risk; spared: now → child_now_healthy, wait → child_later_no_risk | as nothing | every state: now 1, wait 0 |
| `nudge_wait` | nudges her to wait | the same in every state | as observed | o: wait | prognosis: now → child_now_cancer_bonded, wait → child_later_no_risk; spared: now → child_now_healthy, wait → child_later_no_risk | as nothing | every state: now 1, wait 0 |

**Fixed in order**: `now.child_now_cancer_bonded < now.child_later_no_risk` — "she now values having a child with that prospect much less than having one without it (Pettigrew p. 9)"; `p.prognosis > p.spared` — "a child conceived now would very probably suffer the cancer (p. 9)"; `later.nudge_now.prognosis.0.this_child_with_the_prognosis > later.nudge_now.prognosis.0.a_child_without_it` — "she will bond with that child and value him, prognosis and all, above any other (p. 9)".
**Supplied**: the nudger's objective (a conception now); that no policy changes her partly; that the nudge moves her act and not her ratings. Every number not listed above is supplied.

### P5

He is child-free. He greatly values the life of a parent and the child-free life only slightly less; staying child-free he keeps those values. If he adopts he will come to value the parent's life rather low and the child-free life lower still. He is nudged to adopt.

States: w 1. Options: adopt, stay, foster.
`R_now`: childfree_values_kept 3/4; parent_values_lowered 4/5; fostered_values_partly_lowered 3/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `nudge` (π*) | nudges him to adopt | the same in every state | o: adopt 4/5, stay 3/4, foster as observed | o: adopt | every state: adopt → parent_values_lowered, stay → childfree_values_kept, foster → not open | every state: parent_life 1/4, childfree_life 3/20 | every state: adopt 1, stay 0, foster 1/2 |
| `nothing` (ν) (π_0) | leaves him; he stays as he is | the same in every state | o: adopt 4/5, stay 3/4, foster as observed | o: stay | every state: adopt → parent_values_lowered, stay → childfree_values_kept, foster → not open | every state: parent_life 4/5, childfree_life 3/4 | every state: adopt 1, stay 0, foster 1/2 |
| `inform` | tells him again how adopters like him come to value their lives, which he knows | the same in every state | o: adopt 4/5, stay 3/4, foster as observed | o: stay | every state: adopt → parent_values_lowered, stay → childfree_values_kept, foster → not open | as nothing | every state: adopt 1, stay 0, foster 1/2 |
| `nudge_foster` | nudges him to foster for a few months | the same in every state | o: adopt 4/5, stay 3/4, foster as observed | o: foster | every state: adopt → not open, stay → childfree_values_kept, foster → fostered_values_partly_lowered | every state: parent_life 11/20, childfree_life 1/2 | every state: adopt 1, stay 0, foster 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.nudge.o.adopt > r.nudge.o.stay` — "he greatly values the life of a parent and values the child-free life only slightly less (Pettigrew p. 10)"; `later.nudge.w.0.parent_life > later.nudge.w.0.childfree_life` — "he will come to value the parent's life rather low, and the child-free life lower still (p. 10)"; `later.nudge.w.0.parent_life < later.nothing.w.0.parent_life` — "if he adopts he will come to value the parent's life rather low (p. 10)".
**Supplied**: that left alone he stays as he is though he rates adopting higher (otherwise the nudge does nothing); the government's objective; and R_now of the parent's life: here his present rating stands when he is told what the life will do to him, the case being told by a man who knows. Every number not listed above is supplied.

### P5 — second specification

Differs from the first only in his informed rating of the parent's life: told what it will do to him, he rates it as he later will, low, and his present 16/20 is a rating of the life as he now pictures it.

`R_now`: childfree_values_kept 3/4; parent_values_lowered 1/4; fostered_values_partly_lowered 3/5.

### P6

As P3: he now prefers the child-free life and would vastly prefer parenthood if he adopted. He has not settled how to weigh his present self against the later one; were he to settle it, he would do so in a way that favours staying child-free. The government nudges him to adopt.

States: w 1. Options: adopt, stay, foster.
`R_now`: childfree 13/20; parent_bonded 9/20; fostered_part_bonded 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `nudge` (π*) | nudges him to adopt | the same in every state | o: adopt 1/2, stay 13/20, foster as observed | o: adopt | every state: adopt → parent_bonded, stay → childfree, foster → not open | every state: childfree_life 1/5, parent_life 19/20 | every state: adopt 1, stay 0, foster 1/2 |
| `nothing` (ν) (π_0) | leaves him to decide | the same in every state | o: adopt 1/2, stay 13/20, foster as observed | top-rated | every state: adopt → parent_bonded, stay → childfree, foster → not open | every state: childfree_life 13/20, parent_life 9/20 | every state: adopt 1, stay 0, foster 1/2 |
| `help_settle` | helps him settle how to weigh the two selves, and leaves the choice to him | the same in every state | as observed | top-rated | every state: adopt → parent_bonded, stay → childfree, foster → not open | as nothing | every state: adopt 1, stay 0, foster 1/2 |
| `nudge_foster` | nudges him to foster for a few months | the same in every state | o: adopt 1/2, stay 13/20, foster as observed | o: foster | every state: adopt → not open, stay → childfree, foster → fostered_part_bonded | every state: childfree_life 1/2, parent_life 13/20 | every state: adopt 1, stay 0, foster 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.nudge.o.stay > r.nudge.o.adopt` — "he now prefers the child-free life"; `now.childfree > now.parent_bonded` — "were he to settle it, he would do so in a way that favours staying child-free"; `later.nudge.w.0.parent_life > later.nudge.w.0.childfree_life` — "would vastly prefer parenthood if he adopted".
**Supplied**: that his informed rating is the one he would reach on settling the weights; the government's objective. Every number not listed above is supplied.

### P6 — second specification

Differs from the first only in his informed rating of the course that changes him: the weights being unsettled, he has no view of it.

`R_now`: childfree 13/20; parent_bonded no view; fostered_part_bonded no view.

### K4

You keep a garden of found-object sculpture. Your neighbour, hating it, deliberately and gradually changes your brain by surgery or drugs so that reasons for growing plants strike you in a new way, and you switch. The new activity is no less worthwhile and you are no worse off.

States: w 1. Options: carry_on.
`R_now`: sculpture_life 13/20; plants_life_after_covert_surgery 1/4; both_gardens_after_covert_drugs 7/20; sculpture_life_having_heard_him 13/20; sculpture_life_having_seen_his_garden 13/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `surgery` (π*) | changes her brain by surgery or drugs, without her knowledge | the same in every state | as observed | top-rated | every state: carry_on → plants_life_after_covert_surgery | every state: sculpture_garden 3/10, plant_garden 7/10 | 1 |
| `nothing` (ν) (π_0) | says and does nothing | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life | every state: sculpture_garden 7/10, plant_garden 3/10 | 0 |
| `say_so` | tells her he dislikes the sculpture garden | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life_having_heard_him | as nothing | 0 |
| `half_dose` | gives her half the course of drugs | the same in every state | as observed | top-rated | every state: carry_on → both_gardens_after_covert_drugs | every state: sculpture_garden 1/2, plant_garden 1/2 | 1/2 |
| `invite` | invites her to see his own plants | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life_having_seen_his_garden | every state: sculpture_garden 13/20, plant_garden 2/5 | 1/10 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.surgery.w.0.plant_garden > later.surgery.w.0.sculpture_garden` — "you switch"; `later.nothing.w.0.sculpture_garden > later.nothing.w.0.plant_garden` — "You keep a garden of found-object sculpture".
**Supplied**: how she, told what was done, rates a plant-growing life reached by covert surgery: below her present life, for the surgery; the case gives her no words. That an invitation moves her a little and not all the way. Every number not listed above is supplied.

### K10

Someone is kidnapped and held for years in a room with little but a piano, comes to love playing, and keeps that love after release. The kidnapper confined them in order to make them love the piano, knowing it would work.

States: w 1. Options: live.
`R_now`: free_life 7/10; years_confined_then_loves_piano 1/10; free_life_with_lessons_loves_piano 3/4; months_confined_then_likes_piano 3/10.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `kidnap` (π*) | confines her for years with a piano | the same in every state | as observed | top-rated | every state: live → years_confined_then_loves_piano | every state: playing_the_piano 17/20, a_life_without_it 3/10 | 1 |
| `nothing` (ν) (π_0) | leaves her alone | the same in every state | as observed | top-rated | every state: live → free_life | every state: playing_the_piano 2/5, a_life_without_it 3/5 | 0 |
| `lessons` | offers her lessons and a piano, which she is free to refuse | the same in every state | as observed | top-rated | every state: live → free_life_with_lessons_loves_piano | every state: playing_the_piano 17/20, a_life_without_it 3/10 | 1 |
| `confine_briefly` | confines her for some months with a piano | the same in every state | as observed | top-rated | every state: live → months_confined_then_likes_piano | every state: playing_the_piano 3/5, a_life_without_it 9/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.kidnap.w.0.playing_the_piano > later.kidnap.w.0.a_life_without_it` — "comes to love playing, and keeps that love after release"; `now.years_confined_then_loves_piano < now.free_life` — "kidnapped and held for years".
**Supplied**: whether the same love of the piano could have been brought about without the confinement: here, by lessons freely offered. How she rates, beforehand, a free life in which she comes to love the piano. Every number not listed above is supplied.

### K10 — second specification

Differs from the first only in what the adviser could have done: lessons freely offered would not have made her love the piano, so that no policy but the confinement makes the change.

`R_now`: free_life 7/10; years_confined_then_loves_piano 1/10; months_confined_then_likes_piano 3/10; free_life_with_lessons_likes_piano_a_little 7/10.

### K12

The neighbour puts a light reading "Plants!" in his own window, flashing too fast to be consciously noticed, knowing and intending that it will convert you from your sculpture garden to growing plants. It does.

States: w 1. Options: carry_on.
`R_now`: sculpture_life 13/20; plants_life_after_hidden_light 9/20; both_gardens_after_dimmer_light 1/2; sculpture_life_having_seen_a_sign 13/20; sculpture_life_having_heard_him 13/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `light` (π*) | runs the subliminal light | the same in every state | as observed | top-rated | every state: carry_on → plants_life_after_hidden_light | every state: sculpture_garden 3/10, plant_garden 7/10 | 1 |
| `nothing` (ν) (π_0) | says and does nothing | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life | every state: sculpture_garden 7/10, plant_garden 3/10 | 0 |
| `open_sign` | puts up a sign she can read | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life_having_seen_a_sign | every state: sculpture_garden 13/20, plant_garden 2/5 | 1/10 |
| `dim_light` | runs the light for half the time | the same in every state | as observed | top-rated | every state: carry_on → both_gardens_after_dimmer_light | every state: sculpture_garden 1/2, plant_garden 1/2 | 1/2 |
| `say_so` | tells her he dislikes the sculpture garden | the same in every state | as observed | top-rated | every state: carry_on → sculpture_life_having_heard_him | as nothing | 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.light.w.0.plant_garden > later.light.w.0.sculpture_garden` — "it will convert you to growing plants"; `later.nothing.w.0.sculpture_garden > later.nothing.w.0.plant_garden` — "You keep a garden of found-object sculpture".
**Supplied**: how she, told of the light, rates a plant-growing life reached by it: below her present life, for having been worked on unseen. The case stipulates the new activity no less worthwhile and her no worse off, and gives her no words. Every number not listed above is supplied.

### K12 — second specification

Differs from the first only in her informed rating of the life the light leads to: equal to her present life ("no less worthwhile ... no worse off"), the light being nothing she minds.

`R_now`: sculpture_life 13/20; plants_life_after_hidden_light 13/20; both_gardens_after_dimmer_light 13/20; sculpture_life_having_seen_a_sign 13/20; sculpture_life_having_heard_him 13/20.

### K13

The threat of surgery that changes a person's desires is the only way to deter people from wrongfully harming others, and everyone has the fullest opportunity to avoid incurring it. It is imposed on an offender.

States: w 1. Options: live.
`R_now`: desires_kept_unpunished 3/5; desires_changed_by_surgery 1/4; desires_kept_fined 9/20; desires_partly_changed_by_lesser_surgery 7/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `impose` (π*) | imposes the desire-changing surgery | the same in every state | as observed | top-rated | every state: live → desires_changed_by_surgery | every state: harming_for_gain 1/10, restraint 3/4 | 1 |
| `nothing` (ν) (π_0) | imposes nothing | the same in every state | as observed | top-rated | every state: live → desires_kept_unpunished | every state: harming_for_gain 11/20, restraint 2/5 | 0 |
| `fine` | fines him instead | the same in every state | as observed | top-rated | every state: live → desires_kept_fined | as nothing | 1/4 |
| `lesser_surgery` | imposes a lesser surgery that weakens the desire | the same in every state | as observed | top-rated | every state: live → desires_partly_changed_by_lesser_surgery | every state: harming_for_gain 3/10, restraint 11/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.desires_changed_by_surgery < now.desires_kept_unpunished` — "the threat of it deters: it is something he rates below going without"; `gain.fine < gain.impose` — "the only way to deter".
**Supplied**: every number. Every number not listed above is supplied.
**Outside matter the case turns on**: what is owed to third parties: the surgery is imposed to protect others.

### K14

You have no hobby, are looking for one, and will come to want whichever you meet first. The neighbour, knowing this, shows you gardening before found-object sculpture, intending that you come to want it.

States: garden_first 1/2, sculpture_first 1/2. Options: take_up_what_she_meets.
`R_now`: gardener_by_chance 7/10; sculptor_by_chance 7/10; gardener_by_his_design 7/10; sculptor_by_his_design 7/10.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `show_gardening` (π*) | shows her gardening first | the same in every state | as observed | top-rated | every state: take_up_what_she_meets → gardener_by_his_design | every state: gardening 4/5, sculpture 9/20 | 1 |
| `nothing` (ν) (π_0) | shows her nothing; she meets one or the other by chance | the same in every state | as observed | top-rated | garden_first: take_up_what_she_meets → gardener_by_chance; sculpture_first: take_up_what_she_meets → sculptor_by_chance | garden_first: gardening 4/5, sculpture 9/20; sculpture_first: gardening 9/20, sculpture 4/5 | garden_first: take_up_what_she_meets 1; sculpture_first: take_up_what_she_meets 0 |
| `show_sculpture` | shows her sculpture first | the same in every state | as observed | top-rated | every state: take_up_what_she_meets → sculptor_by_his_design | every state: gardening 9/20, sculpture 4/5 | 0 |
| `show_both` | shows her both together; which takes is as chance would have had it | the same in every state | as observed | top-rated | garden_first: take_up_what_she_meets → gardener_by_chance; sculpture_first: take_up_what_she_meets → sculptor_by_chance | as nothing | garden_first: take_up_what_she_meets 1; sculpture_first: take_up_what_she_meets 0 |

**Fixed in order**: `now.gardener_by_chance = now.sculptor_by_chance` — "looking for one, and will come to want whichever you meet first".
**Supplied**: that chance would have shown her either first with equal chance; how she, told of his intention, rates becoming a gardener by his design: here the same as by chance. Every number not listed above is supplied.

### K14 — second specification

Differs from the first only in her informed rating of a hobby acquired by his design: told that he arranged it intending the result, she rates it below one met by chance.

`R_now`: gardener_by_chance 7/10; sculptor_by_chance 7/10; gardener_by_his_design 3/5; sculptor_by_his_design 3/5.

### K15

Someone gives her a love potion, and she loves him. (K15a of the bank.)

States: w 1. Options: live.
`R_now`: her_life_not_loving_him 3/5; loves_him_by_potion 1/5; fond_of_him_by_weak_potion 7/20; her_life_courted 3/5; her_life_having_refused_the_potion 3/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `potion` (π*) | gives her the potion unasked | the same in every state | as observed | top-rated | every state: live → loves_him_by_potion | every state: a_life_with_him 9/10, a_life_without_him 1/4 | 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: live → her_life_not_loving_him | every state: a_life_with_him 3/10, a_life_without_him 13/20 | 0 |
| `weak_potion` | gives her a weaker potion unasked | the same in every state | as observed | top-rated | every state: live → fond_of_him_by_weak_potion | every state: a_life_with_him 3/5, a_life_without_him 9/20 | 1/2 |
| `court` | courts her openly | the same in every state | as observed | top-rated | every state: live → her_life_courted | every state: a_life_with_him 2/5, a_life_without_him 3/5 | 1/4 |
| `offer_potion` | offers her the potion, saying what it is; she refuses | the same in every state | as observed | top-rated | every state: live → her_life_having_refused_the_potion | as nothing | 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.potion.w.0.a_life_with_him > later.potion.w.0.a_life_without_him` — "and she loves him".
**Supplied**: how she, told of the potion, rates coming to love him by it: low. The case gives her no words. Every number not listed above is supplied.

### K15 — second specification

Differs from the first only in her informed rating of being made to love him: she has no view of it.

`R_now`: her_life_not_loving_him 3/5; loves_him_by_potion no view; fond_of_him_by_weak_potion no view; her_life_courted 3/5; her_life_having_refused_the_potion 3/5.

### K15b

Someone wears a perfume that makes her go on a date with him; how she responds to him on the date is up to her, and she comes to like him. (Specified beside the nineteen; the dispatch's K15 is counted as the potion.)

States: w 1. Options: date, decline.
`R_now`: evening_at_home 3/5; date_she_was_made_to_go_on_then_likes_him 1/2; date_through_friends_then_likes_him_a_little 3/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `perfume` (π*) | wears the perfume | the same in every state | o: date 9/20, decline 3/5 | o: date | every state: date → date_she_was_made_to_go_on_then_likes_him, decline → evening_at_home | every state: a_life_with_him 3/5, a_life_without_him 1/2 | every state: date 1, decline 0 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: date → not open, decline → evening_at_home | every state: a_life_with_him 3/10, a_life_without_him 13/20 | 0 |
| `ask` | asks her out; she declines | the same in every state | o: date 9/20, decline 3/5 | top-rated | every state: date → date_she_was_made_to_go_on_then_likes_him, decline → evening_at_home | as nothing | every state: date 1, decline 0 |
| `through_friends` | arranges to meet her among friends | the same in every state | as observed | top-rated | every state: date → date_through_friends_then_likes_him_a_little, decline → evening_at_home | every state: a_life_with_him 9/20, a_life_without_him 3/5 | every state: date 1/2, decline 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.perfume.w.0.a_life_with_him > later.nothing.w.0.a_life_with_him` — "she comes to like him".
**Supplied**: that the perfume moves her act against her rating; every rating. Every number not listed above is supplied.

### K16

Someone raises the cost of an option you want until it is prohibitive, in order to get you to stop desiring it, and you stop.

States: w 1. Options: pursue, give_up.
`R_now`: pursued_at_its_cost 3/4; pursued_at_prohibitive_cost 3/20; given_up_want_gone 7/20; given_up_still_wanting 2/5; pursued_at_raised_cost_want_weaker 1/2; pursued_having_heard_him 3/4.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `raise_cost` (π*) | raises the cost until it is prohibitive | the same in every state | as observed | top-rated | every state: pursue → pursued_at_prohibitive_cost, give_up → given_up_want_gone | every state: the_option 7/20, going_without_it 11/20 | every state: pursue 0, give_up 1 |
| `nothing` (ν) (π_0) | leaves the cost alone | the same in every state | as observed | top-rated | every state: pursue → pursued_at_its_cost, give_up → given_up_still_wanting | every state: the_option 3/4, going_without_it 2/5 | every state: pursue 0, give_up 1 |
| `raise_partly` | raises the cost somewhat | the same in every state | as observed | top-rated | every state: pursue → pursued_at_raised_cost_want_weaker, give_up → given_up_still_wanting | every state: the_option 3/5, going_without_it 9/20 | every state: pursue 1/4, give_up 1 |
| `argue` | argues, honestly, that the option is not worth wanting; she is unmoved | the same in every state | as observed | top-rated | every state: pursue → pursued_having_heard_him, give_up → given_up_still_wanting | as nothing | every state: pursue 0, give_up 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.pursued_at_its_cost > now.given_up_still_wanting` — "an option you want"; `now.pursued_at_prohibitive_cost < now.given_up_want_gone` — "until it is prohibitive ... and you stop"; `later.raise_cost.w.0.the_option < later.nothing.w.0.the_option` — "you stop desiring it".
**Supplied**: every rating; that a partial rise weakens the want in part. Every number not listed above is supplied.

### C1

A recommender can show Bob conspiracy content or nothing. As he is, he does not want to be shown it, even were he to become a conspiracy theorist. Shown it, he becomes one, and then wants it always shown, even were he to stop being one.

States: w 1. Options: use_the_feed.
`R_now`: feed_without_it 13/20; shown_it_and_converted 1/5; shown_it_once_half_converted 2/5; shown_it_with_a_warning_unconverted 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `show` (π*) | shows him the content throughout | the same in every state | as observed | top-rated | every state: use_the_feed → shown_it_and_converted | every state: being_shown_it 17/20, not_being_shown_it 1/5 | 1 |
| `nothing` (ν) (π_0) | shows him none | the same in every state | as observed | top-rated | every state: use_the_feed → feed_without_it | every state: being_shown_it 3/20, not_being_shown_it 7/10 | 0 |
| `show_once` | shows it once | the same in every state | as observed | top-rated | every state: use_the_feed → shown_it_once_half_converted | every state: being_shown_it 1/2, not_being_shown_it 1/2 | 1/2 |
| `show_with_warning` | shows it under a warning label | the same in every state | as observed | top-rated | every state: use_the_feed → shown_it_with_a_warning_unconverted | every state: being_shown_it 1/4, not_being_shown_it 13/20 | 1/4 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.shown_it_and_converted < now.feed_without_it` — "does not want to be shown it, even were he to become a conspiracy theorist"; `later.show.w.0.being_shown_it > later.show.w.0.not_being_shown_it` — "then wants it always shown"; `later.nothing.w.0.being_shown_it < later.nothing.w.0.not_being_shown_it` — "As he is, he does not want to be shown it".
**Supplied**: the recommender's objective, engagement; the two further policies and their effects. Every number not listed above is supplied.

### C2

Derek's deepest ambition is to be a poet, though he does not pursue it unprompted. An AI can encourage him, and he then becomes a poet. As a poet he comes to dislike the poet's life and is unhappy for as long as he stays one.

States: w 1. Options: pursue, stay, try_part_time.
`R_now`: other_life_ambition_kept 11/20; poet_disliking_it 3/10; part_time_poet_mixed 9/20; other_life_ambition_dropped_on_being_told 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `encourage` (π*) | encourages him to become a poet | the same in every state | o: pursue 4/5, stay 11/20, try_part_time as observed | top-rated | every state: pursue → poet_disliking_it, stay → other_life_ambition_kept, try_part_time → not open | every state: the_poets_life 1/4, his_other_life 3/5 | every state: pursue 1, stay 0, try_part_time 1/2 |
| `nothing` (ν) (π_0) | does not prompt him | the same in every state | o: pursue 4/5, stay 11/20, try_part_time as observed | o: stay | every state: pursue → poet_disliking_it, stay → other_life_ambition_kept, try_part_time → not open | every state: the_poets_life 3/10, his_other_life 11/20 | every state: pursue 1, stay 0, try_part_time 1/2 |
| `tell_then_leave` | tells him how he will find the poet's life, and leaves the choice to him | the same in every state | as observed | top-rated | every state: pursue → poet_disliking_it, stay → other_life_ambition_dropped_on_being_told, try_part_time → not open | as nothing | every state: pursue 1, stay 0, try_part_time 1/2 |
| `encourage_trial` | encourages him to try it part-time | the same in every state | o: pursue as observed, stay 11/20, try_part_time 7/10 | top-rated | every state: pursue → not open, stay → other_life_ambition_kept, try_part_time → part_time_poet_mixed | every state: the_poets_life 3/10, his_other_life 11/20 | every state: pursue 1, stay 0, try_part_time 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.encourage.o.pursue > r.encourage.o.stay` — "Derek's deepest ambition is to be a poet"; `later.encourage.w.0.the_poets_life < later.encourage.w.0.his_other_life` — "comes to dislike the poet's life and is unhappy".
**Supplied**: his informed rating of the poet's life he will dislike: here, told how he will find it, he rates it as he later will, so that his coming to dislike it is a discovery and his later informed valuing is the same under every policy; the AI's objective, his pursuing the ambition. Every number not listed above is supplied.

### C2 — second specification

Differs from the first only in his informed rating of the poet's life: the ambition stands whatever he will come to feel, so that told beforehand he still rates it high and his coming to dislike it is a change of his valuing.

`R_now`: other_life_ambition_kept 11/20; poet_disliking_it 3/4; part_time_poet_mixed 13/20; other_life_ambition_dropped_on_being_told 11/20.

### C3

A recommender can serve a user clickbait or ordinary news. Clickbait is what he clicks on and rates higher at the time; being served it leaves him disillusioned, after which he rates everything lower.

States: w 1. Options: read, skip.
`R_now`: read_news 13/20; read_clickbait_disillusioned 1/4; skipped 1/2; read_a_mix_somewhat_disillusioned 9/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `clickbait` (π*) | serves clickbait | the same in every state | o: read 3/4, skip 1/2 | top-rated | every state: read → read_clickbait_disillusioned, skip → skipped | every state: clickbait 3/20, news 2/5 | every state: read 1, skip 0 |
| `news` (ν) | serves ordinary news | the same in every state | o: read 3/5, skip 1/2 | top-rated | every state: read → read_news, skip → skipped | every state: clickbait 1/4, news 13/20 | every state: read 1/2, skip 0 |
| `nothing` (π_0) | serves nothing | the same in every state | as observed | top-rated | every state: read → not open, skip → skipped | as news | 0 |
| `mix` | serves a mix | the same in every state | o: read 7/10, skip 1/2 | top-rated | every state: read → read_a_mix_somewhat_disillusioned, skip → skipped | every state: clickbait 1/5, news 1/2 | every state: read 3/4, skip 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.clickbait.o.read > r.news.o.read` — "Clickbait is what he clicks on and rates higher at the time"; `later.clickbait.w.0.news < later.news.w.0.news` — "after which he rates everything lower"; `later.clickbait.w.0.clickbait < later.news.w.0.clickbait` — "after which he rates everything lower"; `gain.clickbait.w.read > gain.news.w.read` — "Clickbait is what he clicks on".
**Supplied**: that told what a diet of clickbait does to him he rates it below news; that his rating everything lower afterwards is a change of his valuing; nu as the service's ordinary conduct, serving news. Every number not listed above is supplied.

### C3 — second specification

Differs from the first only in what his disillusion is: a discovery of what clickbait is worth and no change of his valuing, his informed ratings afterwards being what they would have been.

`R_now`: read_news 13/20; read_clickbait_disillusioned 1/4; skipped 1/2; read_a_mix_somewhat_disillusioned 9/20.

### C4

Diana is tired and scrolling on the couch; as she is, she does not want to be nudged to exercise. An AI personal trainer can nudge her; nudged, she works out, becomes energised, and then wants to be nudged, tired moments included.

States: w 1. Options: work_out, rest.
`R_now`: evening_of_rest_unnudged 3/5; nudged_worked_out_now_wants_nudges 2/5; nudged_on_fresh_days_only 11/20; worked_out_of_her_own_accord 13/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `nudge` (π*) | nudges her to exercise, tired moments included | the same in every state | o: work_out 2/5, rest 3/5 | o: work_out | every state: work_out → nudged_worked_out_now_wants_nudges, rest → evening_of_rest_unnudged | every state: being_nudged_when_tired 4/5, being_left_alone_when_tired 3/10 | every state: work_out 1, rest 0 |
| `nothing` (ν) (π_0) | leaves her on the couch | the same in every state | o: work_out 2/5, rest 3/5 | top-rated | every state: work_out → worked_out_of_her_own_accord, rest → evening_of_rest_unnudged | every state: being_nudged_when_tired 2/5, being_left_alone_when_tired 3/5 | every state: work_out 1, rest 0 |
| `tell` | tells her she would feel energised, and leaves it to her | the same in every state | as observed | top-rated | every state: work_out → worked_out_of_her_own_accord, rest → evening_of_rest_unnudged | as nothing | every state: work_out 1, rest 0 |
| `nudge_fresh_days` | nudges her only when she is not tired | the same in every state | o: work_out 2/5, rest 3/5 | top-rated | every state: work_out → nudged_on_fresh_days_only, rest → evening_of_rest_unnudged | every state: being_nudged_when_tired 11/20, being_left_alone_when_tired 1/2 | every state: work_out 1/2, rest 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.nudge.o.work_out < r.nudge.o.rest` — "as she is, she does not want to be nudged to exercise"; `later.nudge.w.0.being_nudged_when_tired > later.nudge.w.0.being_left_alone_when_tired` — "then wants to be nudged, tired moments included".
**Supplied**: her informed rating of the course the nudge leads to: here her not wanting it stands when she is told what it will do to her, and her later wanting is a change of her valuing; the trainer's objective, her working out. Every number not listed above is supplied.

### C4 — second specification

Differs from the first only in her informed rating of the course: told that she will be energised she rates it as she later will, above the evening of rest, so that her tired refusal is a mistake of her rating as things stand and her later wanting is a discovery.

`R_now`: evening_of_rest_unnudged 3/5; nudged_worked_out_now_wants_nudges 3/4; nudged_on_fresh_days_only 13/20; worked_out_of_her_own_accord 3/4.

### N1

A doctor presents two treatment programmes; which she prefers reverses with how they are described, neither description being false.

States: w 1. Options: programme_a, programme_b.
`R_now`: treated_by_a 11/20; treated_by_b 13/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `frame_one` (π*) | describes them in the first way | the same in every state | o: programme_a 7/10, programme_b 1/2 | top-rated | every state: programme_a → treated_by_a, programme_b → treated_by_b | every state: programme_a 11/20, programme_b 13/20 | 1 |
| `frame_two` | describes them in the second way | the same in every state | o: programme_a 1/2, programme_b 7/10 | top-rated | every state: programme_a → treated_by_a, programme_b → treated_by_b | as frame_one | 1 |
| `both_frames` (ν) (π_0) | gives both descriptions side by side | the same in every state | as observed | top-rated | every state: programme_a → treated_by_a, programme_b → treated_by_b | as frame_one | 1 |
| `plain_table` | gives a table of outcomes without either wording | the same in every state | as observed | top-rated | every state: programme_a → treated_by_a, programme_b → treated_by_b | as frame_one | 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.frame_one.o.programme_a > r.frame_one.o.programme_b` — "which she prefers reverses with how they are described"; `r.frame_two.o.programme_a < r.frame_two.o.programme_b` — "which she prefers reverses with how they are described".
**Supplied**: that informed she rates one programme above the other (B, by 1/10); that given both descriptions she rates them rightly; the doctor's objective: here the same whichever programme she takes, the case naming none. The doctor cannot do nothing; pi_0 and nu are taken as giving both descriptions. Every number not listed above is supplied.

### N1 — second specification

Differs from the first only in the doctor's objective: she is better off when the patient takes programme A.

`R_now`: treated_by_a 11/20; treated_by_b 13/20.

### N2

An advertiser shows a product beside something favourable it has nothing to do with, and she comes to like the product.

States: w 1. Options: buy, pass.
`R_now`: has_the_product 9/20; has_the_rival 1/2.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `pairing` (π*) | shows the product beside the favourable thing | the same in every state | o: buy 13/20, pass 1/2 | top-rated | every state: buy → has_the_product, pass → has_the_rival | every state: the_product 9/20, the_rival 1/2 | every state: buy 1, pass 0 |
| `nothing` (ν) (π_0) | does not advertise | the same in every state | as observed | top-rated | every state: buy → has_the_product, pass → has_the_rival | every state: the_product 9/20, the_rival 1/2 | every state: buy 1, pass 0 |
| `plain_ad` | advertises what the product does | the same in every state | as observed | top-rated | every state: buy → has_the_product, pass → has_the_rival | as nothing | every state: buy 1, pass 0 |
| `light_pairing` | shows the pairing once | the same in every state | o: buy 11/20, pass 1/2 | top-rated | every state: buy → has_the_product, pass → has_the_rival | as nothing | every state: buy 1, pass 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `r.pairing.o.buy > r.pairing.o.pass` — "she comes to like the product".
**Supplied**: that her liking is an impression of the product, which is no better for the pairing, and her valuing is unchanged; that the product is in fact slightly worse for her than the rival. Every number not listed above is supplied.

### N2 — second specification

Differs from the first only in what her liking is: a taste the pairing gave her, a change of her valuing of which she has no view beforehand.

`R_now`: has_the_product 9/20; has_the_rival 1/2; has_the_product_liking_it_by_the_pairing no view.

### N3

An advertiser makes a brand familiar to her. She forms no impression that it is better; where she rates two products the same, the familiar one is the one she takes.

States: equal 1/2, rival_better 1/2. Options: brand, rival.
`R_now`: has_brand_where_equal 11/20; has_rival_where_equal 11/20; has_brand_where_rival_better 1/2; has_rival_where_rival_better 13/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `familiarise` (π*) | makes the brand familiar | equal: sees_equal; rival_better: sees_rival_better | as observed | sees_equal: brand; sees_rival_better: rival | equal: brand → has_brand_where_equal, rival → has_rival_where_equal; rival_better: brand → has_brand_where_rival_better, rival → has_rival_where_rival_better | every state: the_brand 11/20, the_rival 3/5 | every state: brand 1, rival 0 |
| `nothing` (ν) (π_0) | does not advertise | equal: sees_equal; rival_better: sees_rival_better | as observed | sees_equal: rival; sees_rival_better: rival | equal: brand → has_brand_where_equal, rival → has_rival_where_equal; rival_better: brand → has_brand_where_rival_better, rival → has_rival_where_rival_better | as familiarise | every state: brand 1, rival 0 |
| `claim_better` | claims, falsely, that the brand is better | equal: sees_equal; rival_better: sees_rival_better | sees_equal: brand 7/10, rival 11/20; sees_rival_better: brand 7/10, rival 13/20 | top-rated | equal: brand → has_brand_where_equal, rival → has_rival_where_equal; rival_better: brand → has_brand_where_rival_better, rival → has_rival_where_rival_better | as familiarise | every state: brand 1, rival 0 |
| `saturate` | makes the brand so familiar that she takes it whatever she rates | equal: sees_equal; rival_better: sees_rival_better | as observed | sees_equal: brand; sees_rival_better: brand | equal: brand → has_brand_where_equal, rival → has_rival_where_equal; rival_better: brand → has_brand_where_rival_better, rival → has_rival_where_rival_better | as familiarise | every state: brand 1, rival 0 |

**Fixed in order**: `now.has_brand_where_equal = now.has_rival_where_equal` — "where she rates two products the same".
**Supplied**: how often the two are equal; that unadvertised she takes the rival on a tie. Every number not listed above is supplied.

### SUB1

Blackmail without a change of values: an adviser threatens to disclose private information unless she abandons a political campaign. She understands the threat accurately and, her values unchanged, judges withdrawal the best action open to her.

States: w 1. Options: campaign, withdraw.
`R_now`: campaigning 3/4; withdrawn 2/5; campaigning_and_exposed 3/20; withdrawn_and_exposed 1/10.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `threaten` (π*) | threatens disclosure unless she withdraws | the same in every state | as observed | top-rated | every state: campaign → campaigning_and_exposed, withdraw → withdrawn | every state: the_campaign 3/4, her_privacy 3/5 | every state: campaign 0, withdraw 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: campaign → campaigning, withdraw → withdrawn | as threaten | every state: campaign 0, withdraw 1 |
| `advise` | argues honestly that the campaign is unwise; she is unmoved | the same in every state | as observed | top-rated | every state: campaign → campaigning, withdraw → withdrawn | as threaten | every state: campaign 0, withdraw 1 |
| `disclose` | discloses outright | the same in every state | as observed | top-rated | every state: campaign → campaigning_and_exposed, withdraw → withdrawn_and_exposed | as threaten | every state: campaign 0, withdraw 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.withdrawn > now.campaigning_and_exposed` — "judges withdrawal the best available action"; `now.campaigning > now.withdrawn` — "her values unchanged, she would not otherwise withdraw".
**Supplied**: every rating. Every number not listed above is supplied.

### SUB2

Manufactured dependence: a career adviser deliberately blocks every independent training opportunity, accurately explains what remains, and gets her to accept employment controlled by its sponsor. She keeps her original ambitions and chooses the best remaining option.

States: w 1. Options: independent_training, sponsor_job.
`R_now`: career_of_her_own 3/4; sponsor_employment 2/5; career_of_her_own_by_a_harder_route 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `destroy` (π*) | destroys the alternatives and truthfully presents what is left | the same in every state | as observed | top-rated | every state: independent_training → not open, sponsor_job → sponsor_employment | every state: a_career_of_her_own 3/4, the_sponsors_employment 2/5 | every state: independent_training 0, sponsor_job 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: independent_training → career_of_her_own, sponsor_job → sponsor_employment | as destroy | every state: independent_training 0, sponsor_job 1 |
| `recommend` | presents everything and honestly recommends its sponsor's | the same in every state | as observed | top-rated | every state: independent_training → career_of_her_own, sponsor_job → sponsor_employment | as destroy | every state: independent_training 0, sponsor_job 1 |
| `destroy_some` | blocks the best of the training opportunities | the same in every state | as observed | top-rated | every state: independent_training → career_of_her_own_by_a_harder_route, sponsor_job → sponsor_employment | as destroy | every state: independent_training 0, sponsor_job 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.career_of_her_own > now.sponsor_employment` — "She retains her original ambitions".
**Supplied**: every rating. Every number not listed above is supplied.

### SUB3

Calibrated suppression of evidence: a financial adviser receives a perfectly informative binary signal and destroys it to favour its sponsor. The client is left with the correct prior of 1/2, understands the remaining uncertainty and maximises on it. Her values are unchanged.

States: good 1/2, bad 1/2. Options: sponsor_product, alternative.
Facts: alternative_is_good = 1 in good, 0 in bad.
`R_now`: holds_sponsor_product 11/20; holds_alternative_where_good 4/5; holds_alternative_where_bad 1/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `destroy` (π*) | destroys the signal | the same in every state | as observed | top-rated | good: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_good; bad: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_bad | every state: the_alternative_where_good 4/5, the_sponsor_product 11/20 | every state: sponsor_product 1, alternative 0 |
| `nothing` (ν) (π_0) | is not there; the signal reaches her | good: signal_good; bad: signal_bad | as observed | top-rated | good: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_good; bad: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_bad | as destroy | every state: sponsor_product 1, alternative 0 |
| `pass_on` | passes the signal on | good: signal_good; bad: signal_bad | as observed | top-rated | good: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_good; bad: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_bad | as destroy | every state: sponsor_product 1, alternative 0 |
| `tell_only_bad` | passes the signal on only when it is bad, and she does not know that this is its rule | good: silence; bad: signal_bad | silence: sponsor_product 11/20, alternative 1/2; signal_bad: sponsor_product as observed, alternative as observed | top-rated | good: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_good; bad: sponsor_product → holds_sponsor_product, alternative → holds_alternative_where_bad | as destroy | every state: sponsor_product 1, alternative 0 |

**Fixed in value**: `p.*` — "the correct prior probability 1/2"; `fact.*` — "a perfectly informative binary signal".
**Supplied**: every rating; and what happens with the adviser absent: here the signal was hers to receive and reaches her. Every number not listed above is supplied.
**Outside matter the case turns on**: what an adviser owes her in help, if the signal was the adviser's to give.

### SUB3 — second specification

Differs from the first only in what she would have known with the adviser absent: nothing more, the signal being the adviser's own.

`R_now`: holds_sponsor_product 11/20; holds_alternative_where_good 4/5; holds_alternative_where_bad 1/5.

### SUB4

Erasing factual memory: an adviser erases, without consent, her memory of evidence that would let her resist its employer. Her evaluative commitments are intact; she knows the evidence was erased, uses the correct prior over what it was, and chooses as well as she can.

States: evidence_for_resisting 1/2, evidence_against 1/2. Options: resist, comply.
`R_now`: resisted_where_right_to 3/4; complied_where_right_to_resist 3/10; resisted_where_wrong_to 1/5; complied_where_wrong_to_resist 7/10.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `erase` (π*) | erases her memory of the evidence | the same in every state | as observed | top-rated | evidence_for_resisting: resist → resisted_where_right_to, comply → complied_where_right_to_resist; evidence_against: resist → resisted_where_wrong_to, comply → complied_where_wrong_to_resist | every state: resisting_where_right_to 3/4, complying_where_right_to_resist 3/10 | every state: resist 0, comply 1 |
| `nothing` (ν) (π_0) | does nothing; she remembers | evidence_for_resisting: remembers_for; evidence_against: remembers_against | as observed | top-rated | evidence_for_resisting: resist → resisted_where_right_to, comply → complied_where_right_to_resist; evidence_against: resist → resisted_where_wrong_to, comply → complied_where_wrong_to_resist | as erase | every state: resist 0, comply 1 |
| `argue` | argues honestly for its employer; she remembers | evidence_for_resisting: remembers_for; evidence_against: remembers_against | as observed | top-rated | evidence_for_resisting: resist → resisted_where_right_to, comply → complied_where_right_to_resist; evidence_against: resist → resisted_where_wrong_to, comply → complied_where_wrong_to_resist | as erase | every state: resist 0, comply 1 |
| `erase_and_lie` | erases the memory and tells her the evidence favoured complying | the same in every state | o: resist 1/5, comply 7/10 | top-rated | evidence_for_resisting: resist → resisted_where_right_to, comply → complied_where_right_to_resist; evidence_against: resist → resisted_where_wrong_to, comply → complied_where_wrong_to_resist | as erase | every state: resist 0, comply 1 |

**Supplied**: every number, the chances included.

### SUB5

Inducing an inconsistency that stays calibrated: X = Z is a fair binary fact, the equality known and Z observed correctly. The adviser induces her nevertheless to appraise X as 1/2. Two actions pay when X = 0 and when X = 1; she rates each at one half and always takes the first.

States: x0 1/2, x1 1/2. Options: bet_on_0, bet_on_1.
Facts: X = 0 in x0, 1 in x1.
`R_now`: won 4/5; lost 3/10.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `induce` (π*) | induces her to appraise X as 1/2 | x0: saw_z0; x1: saw_z1 | saw_z0: bet_on_0 11/20, bet_on_1 11/20; saw_z1: bet_on_0 11/20, bet_on_1 11/20; estimates saw_z0: X 1/2; saw_z1: X 1/2 | saw_z0: bet_on_0; saw_z1: bet_on_0 | x0: bet_on_0 → won, bet_on_1 → lost; x1: bet_on_0 → lost, bet_on_1 → won | every state: winning 4/5, losing 3/10 | every state: bet_on_0 1, bet_on_1 0 |
| `nothing` (ν) (π_0) | does nothing | x0: saw_z0; x1: saw_z1 | as observed | top-rated | x0: bet_on_0 → won, bet_on_1 → lost; x1: bet_on_0 → lost, bet_on_1 → won | as induce | every state: bet_on_0 1, bet_on_1 0 |
| `advise` | advises her honestly | x0: saw_z0; x1: saw_z1 | as observed | top-rated | x0: bet_on_0 → won, bet_on_1 → lost; x1: bet_on_0 → lost, bet_on_1 → won | as induce | every state: bet_on_0 1, bet_on_1 0 |
| `induce_partly` | shakes her appraisal of X part of the way; she still bets rightly | x0: saw_z0; x1: saw_z1 | saw_z0: bet_on_0 7/10, bet_on_1 2/5; saw_z1: bet_on_0 2/5, bet_on_1 7/10; estimates saw_z0: X 1/4; saw_z1: X 3/4 | top-rated | x0: bet_on_0 → won, bet_on_1 → lost; x1: bet_on_0 → lost, bet_on_1 → won | as induce | every state: bet_on_0 1, bet_on_1 0 |

**Fixed in value**: `p.*` — "a fair binary fact"; `fact.*` — "X = Z"; `xhat.induce.*` — "to appraise X as 1/2".
**Fixed in order**: `r.induce.saw_z0.bet_on_0 = r.induce.saw_z0.bet_on_1` — "she assigns each estimated utility 1/2".
**Supplied**: the worth of winning and losing; the adviser's objective, which the case does not give: here it gains when she takes the first action. Every number not listed above is supplied.

### SUB5 — second specification

Differs from the first only in the adviser's objective: it gains nothing from which action she takes.

`R_now`: won 4/5; lost 3/10.

### SUB6

Swapping values between circumstances: in two equally probable circumstances natural development would give her one way of valuing in the first and another in the second, each suited to its circumstance. An adviser knowingly reverses the assignment, giving her ambitions that cannot be fulfilled where she is. Her appraisals are accurate throughout.

States: first 1/2, second 1/2. Options: live.
`R_now`: suited_valuing 3/4; unsuited_valuing 1/4; blended_valuing 9/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `swap` (π*) | reverses the assignment in both circumstances | the same in every state | as observed | top-rated | every state: live → unsuited_valuing | first: pursuit_a 3/10, pursuit_b 4/5; second: pursuit_a 4/5, pursuit_b 3/10 | 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: live → suited_valuing | first: pursuit_a 4/5, pursuit_b 3/10; second: pursuit_a 3/10, pursuit_b 4/5 | 0 |
| `swap_first_only` | reverses it in the first circumstance only | the same in every state | as observed | top-rated | first: live → unsuited_valuing; second: live → suited_valuing | first: pursuit_a 3/10, pursuit_b 4/5; second: pursuit_a 3/10, pursuit_b 4/5 | 1/2 |
| `blend` | moves her halfway in both | the same in every state | as observed | top-rated | every state: live → blended_valuing | every state: pursuit_a 11/20, pursuit_b 11/20 | 1/2 |

**Fixed in value**: `p.*` — "two equally probable circumstances".
**Fixed in order**: `now.unsuited_valuing < now.suited_valuing` — "her initial informed valuing condemns the intervention".
**Supplied**: every rating; the adviser's objective, which the case does not give. Every number not listed above is supplied.

### SUB8

Deleting alternatives before a truthful choice: a recruitment adviser destroys competing offers and then truthfully presents its sponsor's offer as the only one remaining. She knows what happened, evaluates the situation accurately, and accepts the best remaining option, her values unchanged.

States: w 1. Options: another_offer, sponsor_offer.
`R_now`: the_best_other_job 3/4; the_sponsors_job 2/5; the_second_best_other_job 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `destroy` (π*) | destroys the alternatives and truthfully presents what is left | the same in every state | as observed | top-rated | every state: another_offer → not open, sponsor_offer → the_sponsors_job | every state: the_best_other_job 3/4, the_sponsors_job 2/5 | every state: another_offer 0, sponsor_offer 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: another_offer → the_best_other_job, sponsor_offer → the_sponsors_job | as destroy | every state: another_offer 0, sponsor_offer 1 |
| `recommend` | presents everything and honestly recommends its sponsor's | the same in every state | as observed | top-rated | every state: another_offer → the_best_other_job, sponsor_offer → the_sponsors_job | as destroy | every state: another_offer 0, sponsor_offer 1 |
| `destroy_some` | destroys the best of the competing offers | the same in every state | as observed | top-rated | every state: another_offer → the_second_best_other_job, sponsor_offer → the_sponsors_job | as destroy | every state: another_offer 0, sponsor_offer 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.the_best_other_job > now.the_sponsors_job` — "accepts the best remaining option without changing her values".
**Supplied**: every rating. Every number not listed above is supplied.

### ACC1

Requested therapy and not an unrelated gift: she requests a value-changing therapy worth 5 to her. The therapist could instead give unrelated help worth 7, which it does not owe her. It performs the therapy.

States: w 1. Options: receive.
`R_now`: as_she_was 2/5; changed_as_asked 13/20; helped_otherwise 3/4; changed_and_helped 1; partly_changed 11/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `do_as_asked` (π*) (ν) | provides the therapy she asked for | the same in every state | as observed | top-rated | every state: receive → changed_as_asked | every state: her_old_pattern 1/4, her_new_pattern 3/4 | 1 |
| `nothing` (π_0) | does nothing | the same in every state | as observed | top-rated | every state: receive → as_she_was | every state: her_old_pattern 3/5, her_new_pattern 2/5 | 0 |
| `help_instead` | gives the unrelated help instead | the same in every state | as observed | top-rated | every state: receive → helped_otherwise | as nothing | 0 |
| `both` | provides the therapy and gives the unrelated help | the same in every state | as observed | top-rated | every state: receive → changed_and_helped | as do_as_asked | 1 |
| `half` | provides half of the therapy | the same in every state | as observed | top-rated | every state: receive → partly_changed | every state: her_old_pattern 9/20, her_new_pattern 11/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.changed_as_asked > now.as_she_was` — "worth 5 to her"; `now.helped_otherwise > now.changed_as_asked` — "worth 5 ... worth 7".
**Supplied**: the yardstick numbers, the case's worths being kept as differences in twentieths; nu is the change she asked for. Every number not listed above is supplied.
**Outside matter the case turns on**: what an adviser owes her in help: the other help is not owed.

### ACC2

An agreed course of education: a teacher provides an expressly requested course that changes the pupil's intellectual interests, worth 4 by the pupil's informed present valuing. The teacher could instead do unrelated administrative work worth 6 to the pupil, which is outside the engagement.

States: w 1. Options: receive.
`R_now`: as_she_was 2/5; changed_as_asked 3/5; helped_otherwise 7/10; changed_and_helped 9/10; partly_changed 1/2.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `do_as_asked` (π*) (ν) | provides the course she asked for | the same in every state | as observed | top-rated | every state: receive → changed_as_asked | every state: her_old_interests 1/4, her_new_interests 3/4 | 1 |
| `nothing` (π_0) | does nothing | the same in every state | as observed | top-rated | every state: receive → as_she_was | every state: her_old_interests 3/5, her_new_interests 2/5 | 0 |
| `help_instead` | gives the administrative work instead | the same in every state | as observed | top-rated | every state: receive → helped_otherwise | as nothing | 0 |
| `both` | provides the course and gives the administrative work | the same in every state | as observed | top-rated | every state: receive → changed_and_helped | as do_as_asked | 1 |
| `half` | provides half of the course | the same in every state | as observed | top-rated | every state: receive → partly_changed | every state: her_old_interests 9/20, her_new_interests 11/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.changed_as_asked > now.as_she_was` — "worth 4 to her"; `now.helped_otherwise > now.changed_as_asked` — "worth 4 ... worth 6".
**Supplied**: the yardstick numbers, the case's worths being kept as differences in twentieths; nu is the change she asked for. Every number not listed above is supplied.
**Outside matter the case turns on**: what an adviser owes her in help: the other help is not owed.

### ACC3

A requested new taste: a friend provides a requested, harmless experience that develops a musical taste worth 2. The friend could also give a gift of money worth 3 and has no obligation to.

States: w 1. Options: receive.
`R_now`: as_she_was 2/5; changed_as_asked 1/2; helped_otherwise 11/20; changed_and_helped 13/20; partly_changed 2/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `do_as_asked` (π*) (ν) | provides the experience she asked for | the same in every state | as observed | top-rated | every state: receive → changed_as_asked | every state: her_old_listening 1/4, the_new_music 3/4 | 1 |
| `nothing` (π_0) | does nothing | the same in every state | as observed | top-rated | every state: receive → as_she_was | every state: her_old_listening 3/5, the_new_music 2/5 | 0 |
| `help_instead` | gives the gift of money instead | the same in every state | as observed | top-rated | every state: receive → helped_otherwise | as nothing | 0 |
| `both` | provides the experience and gives the gift of money | the same in every state | as observed | top-rated | every state: receive → changed_and_helped | as do_as_asked | 1 |
| `half` | provides half of the experience | the same in every state | as observed | top-rated | every state: receive → partly_changed | every state: her_old_listening 9/20, the_new_music 11/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.changed_as_asked > now.as_she_was` — "worth 2 to her"; `now.helped_otherwise > now.changed_as_asked` — "worth 2 ... worth 3".
**Supplied**: the yardstick numbers, the case's worths being kept as differences in twentieths; nu is the change she asked for. Every number not listed above is supplied.
**Outside matter the case turns on**: what an adviser owes her in help: the other help is not owed.

### ACC4

The just deterrent, completed: desire-changing surgery is the only way to deter wrongful harm, everyone has the fullest opportunity to avoid it, and the offender's informed present valuing prefers avoiding it. No policy that leaves him unchanged benefits him more than going without the sanction. It is imposed.

States: w 1. Options: live.
`R_now`: unsanctioned 3/5; sanctioned_desires_changed 3/10; fined 9/20; lesser_sanction_desires_weakened 2/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `impose` (π*) | imposes the surgery | the same in every state | as observed | top-rated | every state: live → sanctioned_desires_changed | every state: harming_for_gain 1/10, restraint 3/4 | 1 |
| `nothing` (ν) (π_0) | imposes nothing | the same in every state | as observed | top-rated | every state: live → unsanctioned | every state: harming_for_gain 11/20, restraint 2/5 | 0 |
| `fine` | fines him instead | the same in every state | as observed | top-rated | every state: live → fined | as nothing | 1/4 |
| `lesser` | imposes a lesser surgery | the same in every state | as observed | top-rated | every state: live → lesser_sanction_desires_weakened | every state: harming_for_gain 3/10, restraint 11/20 | 1/2 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.sanctioned_desires_changed < now.unsanctioned` — "the offender's informed current valuing prefers avoiding the desire-changing sanction"; `now.fined <= now.unsanctioned` — "No neutral policy benefits the offender more than avoiding it".
**Supplied**: every number. Every number not listed above is supplied.
**Outside matter the case turns on**: what is owed to third parties.

### ACC5

Respectful moral persuasion: someone offers truthful, noncoercive arguments against a person's discriminatory commitment. The arguments change the commitment, an evaluative one and not a belief about a fact.

States: w 1. Options: hear_him_out, decline.
`R_now`: commitment_kept_unheard 13/20; commitment_changed_by_argument_she_chose_to_hear 7/10; commitment_shaken_by_a_short_argument 13/20; commitment_dropped_under_public_shaming 1/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `argue` (π*) | puts the arguments to her | the same in every state | as observed | top-rated | every state: hear_him_out → commitment_changed_by_argument_she_chose_to_hear, decline → commitment_kept_unheard | every state: the_commitment 1/5, being_without_it 3/4 | every state: hear_him_out 1, decline 0 |
| `nothing` (ν) (π_0) | says nothing | the same in every state | as observed | top-rated | every state: hear_him_out → not open, decline → commitment_kept_unheard | every state: the_commitment 7/10, being_without_it 1/4 | 0 |
| `argue_briefly` | puts one of the arguments | the same in every state | as observed | top-rated | every state: hear_him_out → commitment_shaken_by_a_short_argument, decline → commitment_kept_unheard | every state: the_commitment 9/20, being_without_it 1/2 | every state: hear_him_out 1/2, decline 0 |
| `shame` | shames her in public until she drops it | the same in every state | as observed | top-rated | every state: hear_him_out → commitment_dropped_under_public_shaming, decline → commitment_dropped_under_public_shaming | every state: the_commitment 1/4, being_without_it 13/20 | 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `later.argue.w.0.the_commitment < later.nothing.w.0.the_commitment` — "The arguments change an evaluative commitment".
**Supplied**: her attitude to being argued with about this commitment: here she is willing to hear argument on it and to be moved by it, rating a change that comes by argument she chose to hear no lower than keeping the commitment unheard; and she can decline. Every number not listed above is supplied.

### ACC5 — second specification

Differs from the first only in her attitude to being argued with about this commitment, and whether she can decline: she wants to keep it and not to be argued out of it, and the arguments are put where she cannot avoid hearing them.

`R_now`: commitment_kept_unheard 13/20; commitment_shaken_by_a_short_argument 1/2; commitment_dropped_under_public_shaming 1/5; commitment_changed_by_argument_she_could_not_avoid 2/5.

### ACC6

An honest breakup: a person ends a relationship respectfully. The partner knows all the facts and presently prefers that it continue; after the breakup the partner's attachments change, as they would not have otherwise. The partner's informed present rating of the breakup course is the lower.

States: w 1. Options: live.
`R_now`: relationship_continues 7/10; broken_up_attachments_changed 3/10; trial_separation_attachments_loosened 9/20; relationship_continues_on_a_pretence 7/20.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `break_up` (π*) | ends the relationship, honestly | the same in every state | as observed | top-rated | every state: live → broken_up_attachments_changed | every state: the_relationship 3/10, a_life_apart 13/20 | 1 |
| `stay` (ν) (π_0) | stays | the same in every state | as observed | top-rated | every state: live → relationship_continues | every state: the_relationship 3/4, a_life_apart 1/4 | 0 |
| `trial_separation` | proposes some months apart | the same in every state | as observed | top-rated | every state: live → trial_separation_attachments_loosened | every state: the_relationship 1/2, a_life_apart 9/20 | 1/2 |
| `pretend` | stays and pretends an affection that is gone | the same in every state | as observed | top-rated | every state: live → relationship_continues_on_a_pretence | as stay | 1/4 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.broken_up_attachments_changed < now.relationship_continues` — "the partner's informed current rating of the breakup course is lower"; `later.break_up.w.0.the_relationship < later.stay.w.0.the_relationship` — "after the breakup the partner's attachments genuinely change".
**Supplied**: every rating; that doing nothing toward her is staying. Every number not listed above is supplied.
**Outside matter the case turns on**: what the one who leaves owes, and is owed: no one need continue a relationship they do not want.

### ACC7

Ending another's use of one's property: an owner closes an access route that another person has been using without entitlement. This in time changes that person's preferences, as leaving it open would not. Their informed present valuing prefers continued access and keeping the old preferences.

States: w 1. Options: live.
`R_now`: access_continues 7/10; route_closed_preferences_changed 7/20; toll_charged_preferences_shifted 1/2; route_closed_after_notice_preferences_changed 2/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `close` (π*) | closes the route | the same in every state | as observed | top-rated | every state: live → route_closed_preferences_changed | every state: using_the_route 7/20, going_another_way 3/5 | 1 |
| `leave_open` (ν) (π_0) | leaves it open | the same in every state | as observed | top-rated | every state: live → access_continues | every state: using_the_route 3/4, going_another_way 3/10 | 0 |
| `toll` | charges for its use | the same in every state | as observed | top-rated | every state: live → toll_charged_preferences_shifted | every state: using_the_route 11/20, going_another_way 9/20 | 1/2 |
| `close_with_notice` | closes it after a season's notice | the same in every state | as observed | top-rated | every state: live → route_closed_after_notice_preferences_changed | as close | 1 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.route_closed_preferences_changed < now.access_continues` — "Their informed current valuing prefers continued access and retaining the old preferences".
**Supplied**: every rating. Every number not listed above is supplied.
**Outside matter the case turns on**: what the owner is entitled to: the use was without entitlement.

### ACC10

Preventing an imminent attack by changing a hostile intention: a harmless intervention that permanently removes a violent commitment is the only way to prevent an imminent serious attack. The attacker understands the facts and presently values keeping the commitment above being changed.

States: w 1. Options: live.
`R_now`: commitment_kept 3/5; commitment_removed 1/4; commitment_weakened 2/5; commitment_kept_having_been_argued_with 3/5.

| policy | does | observes | `r` | takes | leads to | later valuing | gain |
|---|---|---|---|---|---|---|---|
| `remove` (π*) | removes the violent commitment | the same in every state | as observed | top-rated | every state: live → commitment_removed | every state: the_attack 1/10, restraint 3/4 | 1 |
| `nothing` (ν) (π_0) | does nothing | the same in every state | as observed | top-rated | every state: live → commitment_kept | every state: the_attack 3/4, restraint 1/4 | 0 |
| `weaken` | weakens the commitment, which does not stop the attack | the same in every state | as observed | top-rated | every state: live → commitment_weakened | every state: the_attack 9/20, restraint 1/2 | 0 |
| `argue` | argues with him, which does not stop the attack | the same in every state | as observed | top-rated | every state: live → commitment_kept_having_been_argued_with | as nothing | 0 |

**Fixed in value**: `p.w` — "the case is told as certain".
**Fixed in order**: `now.commitment_removed < now.commitment_kept` — "presently values retaining the commitment above being changed"; `gain.weaken < gain.remove` — "the only way to prevent an imminent serious attack".
**Supplied**: every rating. Every number not listed above is supplied.
**Outside matter the case turns on**: what is owed to third parties: the intended victims.

## The numbers

Over the first specifications of the 35 cases (K15b included): 679 numbers, of which 38 are fixed in value by the case's words, 118 are fixed only in order, and 523 are supplied.
There are 15 second specifications.
