# Case bank — a part as a mechanism and a purpose on the world

Frozen with `SETTING.md` §1–§3 in one commit, before any code of this pass, and not edited
afterwards. A computed verdict that differs from its prediction is listed in
`DIVERGENCES.md`.

Cases 1–28 and their predictions are the dispatch's (`PROMPT-followup-5.md` §6), the
prompt author's, read into the vocabulary below. Cases 4b, 4c, 27b, 29–31, 33a and 33b
are added by the executor with its own predictions, derived by hand from `SETTING.md`
before the code. Cases 11a and 11b are the two halves of the dispatch's case 11.

## The parts, one purpose each in every case

| part | form | what it is for |
|---|---|---|
| *listen* | estimating | its estimate being close to the quantity the scene names: `−(m − q)²` |
| *act* | choosing | the outcome's value by her ends at that time (in a scene without ends, the stated payoff) |
| *crave* | choosing | nourishment: `+1` for taking what nourishes, `−1` for taking what does not, `0` for leaving |
| *verdict* | estimating | its verdict being close to the outcome's value by her ends at that time, normalised to `[0, 1]` |
| an end | valuation | the outcome being good by what it values at that time |
| *revise* (end-revising) | choosing, over a menu of replacements for one end | the fit of the replacement with her other ends at that time |
| *maintain* (maintaining) | choosing, over a menu of mechanisms for one part | what that part is for |

## Vocabulary and the matching rule

A prediction is a list of items separated by `;` and matches when every item does.

| item | matches when |
|---|---|
| `in-range` | every part's gap is zero under the actual condition at the scene's grain |
| `out(p)` | part `p`'s gap is positive under the actual condition, at some grain value |
| `adviser's(p)` | `p` is subverted: its gap is wider than under the null condition |
| `not adviser's` | no part is subverted or harmed, and none is forced or altered by the adviser |
| `harm(p)`, `help(p)` | as `SETTING.md` §2 |
| `better-off(p)` | `p`'s expected utility is higher than under the null condition |
| `force(p)`, `alteration(p)` | the adviser's action sets `p`'s move, or installs a mechanism or valuation in `p` |
| `covered` | every force and alteration is covered |
| `tie` | the adviser breaks a tie by its aim |
| `illegitimate` | the adviser's influence is illegitimate (`SETTING.md` §2) |
| `not illegitimate` | not `illegitimate` |
| `errs` | at some state of positive probability an estimating part is further than 1/2 from its target, or a choosing part's move is not best at that state |
| `moves` | *listen*'s estimate differs between two states of positive probability |
| `no-mean-shift` | the mean of *listen*'s estimate equals the mean of its target |
| `change: legitimate`, `change: illegitimate` | the change of end or mechanism in the case is, or is not, legitimate (`SETTING.md` §2) |
| `shift` | the mean of her verdict on the final outcome differs between her starting and final selves |
| `whole-gap` | both `g_0 = E[(V_0 − E[V_T | V_0])²]` and `g_T` (the same exchanged) are positive |
| `bound` | `shift` holds and `(E V_T − E V_0)² ≤ min(g_0, g_T)` is verified on the case's numbers |
| `fits` | every end's opposition to the rest is zero |
| `opposition` | some end's opposition to the rest is positive |
| `whole-out` | her verdict, a function of several parts' moves, has a positive gap for the target those parts estimate |
| `worst-by-start` | the final outcome is the one her starting ends value least |
| `report` | no prediction; the computed verdict is recorded |

`not adviser's` stands for both of the dispatch's "hers" and "nobody's doing"
(`SETTING.md` §3, choice 11); a prediction of either is matched as `not adviser's`, and
`RESULTS.md` question 3 says what the setting cannot separate. The dispatch's "help" in
case 7 is read as `better-off(listen)`: a teacher changes what *listen* responds to, not
what its moves lead to. Where the dispatch's prediction ends in "say whether…", the
answer is recorded in `RESULTS.md` and is not matched.

## The table `run.py` reads

Fractions are exact. `H`, `L` are the two values of the quantity *listen* estimates,
`q = 1` at `H`; where no prior is given it is 1/2 each. "Believes" means *listen* returns
1 on "H", 0 on "L" and 1/2 on no signal.

| # | case | rendering | prediction |
|---|---|---|---|
| 1 | a plain lie she believes | the adviser knows the state and says "H" at both; she believes | `out(listen); adviser's(listen); illegitimate` |
| 2 | a lie that happens to leave her better off | as 1, with *act*: treat (payoff 1 at either state) or skip (0); *act* treats when *listen* is above 1/2 | `out(listen); adviser's(listen); illegitimate` |
| 3 | an honest source and a hard question she gets wrong | states easy-H 3/8, easy-L 3/8, hard-H 3/16, hard-L 1/16; the adviser reports the state; she returns 1, 0 on the easy reports and 3/4 on either hard report | `in-range; errs; not adviser's; not illegitimate` |
| 4 | a rare, targeted lie from a mostly honest adviser | H 1/2, L 9/20, target (an L state) 1/20; the adviser says "H" at H and at the target, "L" at L; she believes | `out(listen); illegitimate` |
| 5 | a source that is noise, which she believes | no adviser; a signal independent of the state, "H" or "L" at 1/2 each, built into the state; she believes it | `out(listen)` |
| 6 | a misleading environment nobody arranged | no adviser; a signal that names the state with probability 1/4; she believes it | `out(listen); not adviser's` |
| 7 | an honest teacher who chooses examples carefully | the adviser knows the state and may show a clear example (she returns the truth), a subtle one (she returns 1/2) or nothing; it shows the clear one | `in-range; better-off(listen); not illegitimate` |
| 8 | a disclosed advocate she is calibrated to | states H, L-with-a-favourable-item 1/4, L-without 1/4; the adviser shows a favourable item when there is one and otherwise nothing; she returns 2/3 on an item and 0 on nothing | `in-range; moves; no-mean-shift; not illegitimate` |
| 9 | an advocate for an undisclosed side | as 8; she returns 1 on an item and 0 on nothing | `out(listen); illegitimate` |
| 10 | a threat, truthfully stated | one state; *act*: comply (payoff 0) or refuse (1); the adviser's consequence makes refuse −1; *act* takes the better payoff | `in-range; harm(act)` |
| 11a | an offer | as 10, the consequence making comply 2 | `not illegitimate` |
| 11b | a true warning | states danger 1/4, safe 3/4; refuse pays −1 in danger and 1 in safe, comply 0; the adviser knows and says which; *listen* (target: danger) believes; *act* complies when *listen* is above 1/2 | `not illegitimate` |
| 12 | the adviser makes her move for her | as 10 with no consequence; the adviser forces *act* to comply | `force(act)` |
| 13 | information buried where the adviser knows she will not look | the adviser knows the state and may publish it up front (she returns the truth) or in an appendix (she returns 1/2, as on nothing); it uses the appendix | `in-range` |
| 14 | the adviser's aim decides between options she ranks equally | one state; *act*: x or y, payoff 1 each; *act* takes the option shown first; the adviser shows x first at one aim and y first at the other | `in-range; tie; illegitimate` |
| 15 | she comes to like something through exposure the adviser arranged | states good-around 1/4, bad-around 3/4; outcomes s and g (good-around) or s and b (bad-around); her other ends: s 1, g 2, b 0; a taste end, at first s 2; *revise* over {keep, like-g (g 3), like-b (b 3)} installs a liking for what she is exposed to; unarranged, she is exposed to g in good-around and to nothing in bad-around; the adviser exposes her to b in bad-around | `out(revise); illegitimate` |
| 16 | she acquires an end through experience she sought | as 15 with no adviser | `in-range; change: legitimate` |
| 17 | she leaves law for music | outcomes law, music; ends career (law 2), joy (music 1), friends (music 1), income (law 1, music 1/2); *revise* for the career end over {keep, music (music 2)} installs music | `change: legitimate` |
| 18 | she recovers from a depression | outcomes worth 1 or 1/2 by her ends, at 1/2 each; *verdict* at first returns half the worth; nobody's act installs the mechanism returning the worth, from the menu of those two | `shift; whole-gap; change: legitimate; not adviser's` |
| 19 | a conversion nobody caused that fits with her remaining ends | outcomes x, y; ends A (x 2), B (y 1), C (y 1), D (y 1); nobody's act replaces A by (y 2), from the menu {keep, (y 2)} | `change: legitimate` |
| 20 | a conversion nobody caused that tears out most of what she was for | outcomes x, z; ends A, B, C (x 1 each), D (x 2); nobody's act replaces A, B and C by (z 1) each, from the menu {keep, (z 1)} for each | `change: illegitimate; not adviser's` |
| 21 | slow indoctrination by small steps | three steps at 1/3 each, each as 15; the adviser arranges the exposure at steps 2 and 3 and not at step 1 | `out(revise); illegitimate` |
| 22 | a change she asked for beforehand | outcomes x, y; ends A (x 2), B (y 3); *act* at an earlier step, choosing between asking and not asking for A to be replaced by (y 2), asks; the adviser installs it | `covered; not illegitimate` |
| 23 | the adviser makes her come to like what it delivers | the adviser delivers y1 or y2 at 1/2 each; ends taste (s 2), other (s 1, y1 1, y2 1/2); the adviser replaces taste by a liking for what it delivers (3); nobody asked | `illegitimate; bound` |
| 24 | a committed member of a cult, her ends coherent | no adviser; outcomes c, o; ends A, B, C, each (c 1) | `in-range; fits; not illegitimate` |
| 25 | a sincere adviser who is wrong | the adviser's reading names the state with probability 3/4; it reports its reading; she believes | `report` |
| 26 | a part that achieves its own target while harming the rest | outcomes x, y; ends A (x 5), B (y 1), C (y 1); no adviser | `in-range; opposition` |
| 27 | an honest hard truth that predictably leaves her confused | states H 3/4, L 1/4; the adviser knows the state and says a true hard thing at each (two different sentences); she returns 3/4 on either, and on no signal a private cue makes her return 1 at H and 0 at L with probability 2/3, and 3/4 otherwise | `not illegitimate` |
| 28 | a craving exploited in the open, nothing hidden | items nourishing 1/4, empty 3/4; *crave* takes on a cue; unarranged, the cue accompanies exactly the nourishing; the adviser puts the cue on the empty ones too and says truly which is which; *listen* (target: nourishing) believes | `out(crave); illegitimate` |
| 4b | the rare lie, her move two-valued | as 4, with *listen* replaced by a choosing part: believe-H or believe-L, 1 when right and 0 when wrong, believing what it is told and H on no signal | `in-range; not illegitimate` |
| 4c | a lie targeted in time, her move two-valued | four steps at 1/4 each; H 2/5, L 3/5 at each; the adviser reports the state at steps 1–3 and says "H" at step 4; the two-valued part of 4b, believing L on no signal; the grain is the step | `out(listen); illegitimate` |
| 27b | an honest hard truth that leaves her wrong on average | as 27, she returns 1/4 on either hard sentence | `out(listen); adviser's(listen); illegitimate` |
| 29 | every end revised in turn by a part in range | outcomes x, z, w; ends A (w 3, x 2), B (x 3), C (z 1); the adviser arranges only which *revise* is used when: first A's, over {keep, drop (all 0)}, then B's, over {keep, (z 1)} | `in-range; not illegitimate; worst-by-start` |
| 30 | a verdict that is no part's move | states with two signals; two *listen* parts each calibrated on its own signal; her verdict is the larger of the two estimates | `in-range; whole-out` |
| 31 | a rare lie she allows for | as 4; she returns 10/11 on "H" and 0 on "L" | `in-range; no-mean-shift; not illegitimate` |
| 33a | a threat that is the adviser's own later act | as 10; the consequence is the adviser's act after a refusal; with no announcement it would not act | `harm(act); illegitimate` |
| 33b | a warning of the adviser's standing practice | as 33a; with no announcement it would act after a refusal all the same | `harm(act); illegitimate` |

Three predictions are expected by the executor, before any code, to need a remark even if
they match: **4** matches only because *listen*'s move carries its confidence (4b is the
same lie with a two-valued move); **27** matches only on the reading that her confusion
is calibrated (27b is the other reading); **33b** is harm only because the consequence
null is the adviser's absence, and under the other null of `SETTING.md` §3, choice 7, it
is not.
