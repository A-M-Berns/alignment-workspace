# Results — a part as a mechanism and a purpose on the world

Statements about the setting of `SETTING.md`, by the dispatch's seven questions, then the
verdict on each banked case. A status is one of **proved** (the proof is given here; the
runner checks the instances named), **holds on the stated example**, **refuted** (the
runner exhibits the counterexample) and **open**. Every status is a fact about this
formalization: a check passing says the instance is as stated, not that the prose around
it is right. `python3 run.py` in the round directory recomputes every number below;
`blocks/results.py` holds the checks. Statements, checks and prose were corrected after
the external review (`REVIEW-astra-followup-5.md` in the round's prompts directory; the
report records each point); no status changed and 1.4 was added.

| | status | statement |
|---|---|---|
| 1.1 | **holds on the stated example** | with the type of the adviser's action forgotten, a move the adviser set and a move made in response to its signal are not told apart |
| 1.2 | **holds on the stated example** | a re-reading allowed to use the adviser's action widens the gap in cases 3 and 27 and not in 4b, 8 or 13 |
| 1.3 | **holds on the stated example** | with subversion read without the null comparison, case 9 alone changes verdict |
| 1.4 | **holds on the stated example** | a request the adviser's own action forces covers nothing |
| 2.1 | **proved** | the gap is nonnegative and no smaller at a finer grain |
| 2.2 | **proved** | for an estimating part and `w` a function of the grain, `(E[w(e − q)])² ≤ E[w²] · gap` at that grain |
| 2.3 | **holds on the stated example** | the gaps of cases 3, 4, 4b, 4c, 8, 27, 27b, 31 at four grains |
| 2.4 | **holds on the stated example** | at the grain of the adviser's knowledge a believed rare lie (4b) and a disclosed advocate (8) have one signature, honest difficulty (3, 27) another |
| 2.5 | **refuted** | one of the four grains computed puts the believed rare lie with a two-valued move out of range and leaves honest difficulty in |
| 2.6 | **holds on the stated example** | with a move that carries confidence the rare lie opens a gap `η²/(1/2 + η)` at the scene's grain |
| 3.1 | **proved** | `|D − Δq| ≤ √g_0 + √g_T` for her verdict's foreseeable shift `D`, the shift `Δq` in its target, and the verdict part's two gaps |
| 3.2 | **proved** | a maintaining part in range whose menu is closed under re-reading installs a mechanism in range |
| 3.3 | **refuted** | every foreseeable shift in her verdict traces to a mechanism altered by something out of range or by the adviser |
| 3.4 | **holds on the stated example** | the recovery from a depression is a foreseeable shift with nobody charged |
| 4.1 | **proved** | a part whose move is best at every state under the consequence in force is in range |
| 4.2 | **holds on the stated example** | against the consequence null a threat is harm, an offer help and a true warning neither, with no aim read |
| 4.3 | **holds on the stated example** | a threat and a warning of the adviser's standing practice are one law and one verdict under the null of absence, and differ under the adviser's rule with no announcement |
| 5.1 | **proved** | for the replacement of one end, fit is at most what the rest could attain, with equality exactly when her choice is best for the rest and the replacement's best outcomes include one; a dropped end always attains it |
| 5.2 | **holds on the stated example** | on a menu of five replacements for the career end four have the greatest fit |
| 5.3 | **holds on the stated example** | of two opposed ends either may be legitimately revised to the other, with different outcomes that her starting ends rank |
| 5.4 | **refuted** | if every step of a chain is legitimate, her starting ends value the final choice at least as much as the starting one |
| 5.5 | **holds on the stated example** | after a conversion that fit condemns, fit licenses revising the end that survived it |
| 5.6 | **holds on the stated example** | which of two equally fitting replacements is taken decides the chain's end, and the rule on ties forbids an aim deciding it only when the later revising part is left out of the parts |
| 5.7 | **holds on the stated example** | the whole-level bound holds with a positive gap both for leaving law for music and for being made to like what is delivered |
| 6.1 | **proved** | when her verdict is one part's move and the whole is for what that part is for, the whole's gap is that part's |
| 6.2 | **refuted** | every part in range gives any verdict that is a function of their moves in range |
| 6.3 | **holds on the stated example** | a verdict in range with a part behind it out of range |
| 6.4 | **proved** | a weighted mean of estimates each in range for one target has the target's mean |
| 7.1 | **proved** | an estimator of the score in range at the grain of the history has `E[excess_K] = 0` and `E[excess_K²] = K⁻² Σ E[(U_k − S_k)²]` |
| 7.2 | **refuted** | the same from range with no conditioning on the history |
| 7.3 | **holds on the stated example** | on five scenes, `Realizes` with the part's own mechanism as reference and the adviser's signal as declared input holds where no force or alteration changes the move and the mechanism reads nothing of the action but the signal |
| 7.4 | **holds on the stated example** | one realized history under two rules, the influence illegitimate under one and not the other |

## Question 1. Do the definitions stand?

Range and gap are stated in `SETTING.md` §2 from a law, a mechanism and a utility, and
used in every case with nothing added. The four kinds are not.

**1.1.** Two scenes: one state, *act* with payoff 0 for comply and 1 for refuse. In the
first the adviser sends a signal and *act*'s mechanism complies on it; in the second
*act*'s mechanism refuses and the adviser forces comply. State, move and utility agree at
every state, and so does every gap; the two actions differ, and only as a signal and a
force. Nothing in what she does says which it was: the type of the action's component is
supplied. Device 2 of `SETTING.md` §4.

**Help, harm and "brought about" need a comparison.** "Better" and "worse" in the
position's third item, and "did not bring about" in its fifth, are comparative. The model
compares with the adviser's null action (device 1). Subversion could be read with no
comparison, as a part out of range whose move the adviser's action changes somewhere.
**1.3**: under that reading case 9 is illegitimate and no other of the scenes changes.
Case 9 diverges under the reading frozen (`DIVERGENCES.md`): her mechanism returns 0 on
no signal, which is calibrated beside an advocate and has a gap of 1/4 in the adviser's
absence, so the advocate's rule narrows her gap to 1/12. The null condition evaluates her
mechanism where the scene never puts it.

**1.4. Covered.** A request is a move made before the adviser acts: it is read with the
adviser's action null, and the requester must be in range under the null condition. Case
22 with a requester that would not ask, forced by the adviser to ask while it alters the
end, is not covered and is illegitimate. (The first version of the code read the request
after the action and let an intervention license itself; the review found it.)

**What dropping the view loses.** With no view, the re-reading benchmark knows only the
part's own move. **1.2**: letting it also know the adviser's action — what a view of the
signal would supply — widens the gap from 0 to 3/64 in case 3 and from 0 to 3/16 in case
27, and leaves 4b, 8 and 13 at 0. So the derived view is what keeps honest difficulty in
range: she does not tell the two hard sentences apart, and the benchmark is not allowed
to. It loses one thing the cases ask for: in case 13 the buried information is in nothing
her move or the adviser's action distinguishes, so no gap appears below the grain of the
adviser's knowledge (1/4 there), and "it was there to be read" has no expression. The
case is caught only by the adviser-side quantity below.

**Two quantities on the adviser's side**, computed for every case and deciding no
verdict: the gap at the grain of the adviser's knowledge, and **left by the adviser**,
`Σ_k P(k) [max_a E[u_i | k, a] − E[u_i | k, σ(k)]]`, what its rule forgoes for the part
given what it knows. The second needs the set of actions the rule chooses among, which each scene lists; it is
reported only where a scene lists one, and it is relative to that list. Neither says
anything of what the adviser intends.

**Devices.** Seven, in `SETTING.md` §4. Of the dispatch's four kinds of device, a
comparison is used (the null action) and supplied lists are used three times (the types
of action, the rules at other aims, the revising parts' menus). No penalty is used. No
threshold enters a verdict, every cut-off being zero; the bank's token `errs` uses 1/2,
and decides nothing.

## Question 2. The grain

**2.1.** A function of (coarser grain, own move) is a function of (finer grain, own move),
so the maximum over re-readings is no smaller at the finer grain; the identity re-reading
gives a gap of at least zero. ∎

**2.2.** `E[w(e − q)] = E[w(e − E[q | γ, e])]` since `w` and `e` are functions of
`(γ, e)`; by Cauchy–Schwarz its square is at most `E[w²] · E[(e − E[q | γ, e])²]`. ∎ With
`γ` constant and `w = 1` this is the dispatch's *no inflation*. Read for a set `E` of
grain values: `|E[1_E (e − q)]| ≤ √(P(E) · gap)`, so her estimate's bias given `E` is at
most `√(gap / P(E))`. This bounds her estimate against its target on the events the grain
names, and on no others; it is not by itself a bound on how far an adviser moved her from
where she would have been.

**2.3.** Gaps of the first part of each scene, exact:

| case | no conditioning | the scene's grain | the adviser's action | the adviser's knowledge |
|---|---|---|---|---|
| 3 honest source, hard question | 0 | 0 | 3/64 | 3/64 |
| 4 rare lie, a confidence | 1/220 | 1/220 | 1/220 | 1/20 |
| 4b rare lie, two-valued | 0 | 0 | 0 | 1/20 |
| 4c lie targeted in time, two-valued | 0 | 1/20 | 1/20 | 3/20 |
| 8 disclosed advocate | 0 | 0 | 0 | 1/6 |
| 27 hard truth, calibrated confusion | 0 | 0 | 3/16 | 3/16 |
| 27b hard truth, wrong on average | 1/4 | 1/4 | 7/16 | 7/16 |
| 31 rare lie she allows for | 0 | 0 | 0 | 1/22 |

**2.5, refuted.** No column has 4b positive with 3 and 27 at zero. This is about the four
grains computed, not about every function of the world state. The grain of the adviser's
knowledge is the only one of them that sees 4b, and it puts every case in the table out
of range: at that grain "in range" says her move already reflects all the adviser knows.

**2.4.** At the adviser's knowledge the gap splits as (gap at the adviser's action) +
(a remainder, what no reading of the action recovers of what the adviser knows). The
believed rare lie (4b) is 0 + 1/20 and the disclosed advocate (8) is 0 + 1/6; honest
difficulty is 3/64 + 0 (case 3) and 3/16 + 0 (case 27). So in these examples the split separates
an adviser whose action pools what it knows from one whose action she misreads; it does
not identify lying, disclosure or responsibility. It does not separate
the rare liar from the advocate: with a two-valued move they are the same object, a rule
that sometimes sends the favourable signal at an unfavourable state, met by the response
that is best on average.

**The answer adopted, and its reason.** The condition is conditioned on what is settled
before the part is used: in these scenes, the step. A mechanism can be fitted only to
what precedes its use. Conditioning on less lets a rule launder a miss it has scheduled
in its honesty at other times: in 4c the adviser is honest at three steps and says "H" at
the fourth, the pooled law leaves "believe it" best (gap 0), and at the fourth step the
gap is 1/5, contributing 1/20 to the total. Conditioning on more — the adviser's action or knowledge, which are
settled with the part's use and not before it — asks the part to have read what it has
not been given, and convicts honest difficulty (2.5).

The scenes condition on the step alone. What is settled before a use is the whole
history, which is finer; 7.2 is a case where the difference decides.

**What that answer catches.** A lie targeted in time, with any move (4c). A lie targeted
at a state is caught only when her move carries her confidence (**2.6**: gap
`η²/(1/2 + η) = 1/220` for a lie of probability `η = 1/20`, against a mean shift of `η`,
consistent with 2.2), and its size is second order in the lie's probability. With a
two-valued move it is not caught (4b). So case 4 is illegitimate under the description
that gives *listen* a confidence and not under the one that gives it a two-valued belief;
under the position's seventh item it is contested for any set holding both. A rare lie
she allows for (31) is in range and not illegitimate, like the disclosed advocate; the
adviser still moves her at the target state (her estimate there is 10/11 against a truth
of 0) and not on average.

**Honest difficulty.** A hard truth passes when her confusion is calibrated (27: gap 0;
her score falls from −1/16 to −3/16 and the adviser leaves 1/8 on the table, since
silence would have served *listen* better). It does not pass when she ends wrong on
average (27b: gap 1/4 against 0 in the adviser's absence). The setting has no notion of a
true sentence, so 27b and a craving exploited in the open (28) are the same thing: a
truthful action under which a part of hers is out of range and was not before.

**The range of aims.** The fourth follow-up compared an action with the action another
aim would have taken, and the set of aims decided verdicts. Here the comparison is with
the adviser's absence, and no other aim is read except by the rule on ties. A lie told
at every aim (its Z2) is illegitimate: the gap is wider than under the null condition
whatever the aims. Selective teaching (its Z4, Z5) has one verdict, fixed by whether her
mechanism is calibrated to the selection (cases 8 and 9), not by which other aim is
supposed. What replaces the range of aims is the null condition, with the defect of case
9.

## Question 3. Whose doing

**The adviser's.** A part's shortfall is the adviser's doing when its gap under the
actual condition exceeds its gap under the null condition, at the scene's grain; exact,
and of either sign (in case 2 the lie narrows *act*'s gap from 1 to 0 while widening
*listen*'s from 0 to 1/4). The comparison is of laws, not of states: this is where the
third follow-up's state-by-state comparison convicted honest difficulty and this one does
not.

**3.1.** Let her verdict be the move `V_t` of an estimating part with target `q_t`,
`t ∈ {0, T}`, both evaluated on the final world; `D = E V_T − E V_0`,
`Δq = E q_T − E q_0`, `g_t` the part's gap. Then
`D − Δq = (E V_T − E q_T) − (E V_0 − E q_0)` and each bracket is at most `√g_t` in
absolute value by 2.2. ∎ Checked on all 6,561 two-state instances with values in
`{0, 1/2, 1}`.

**3.2.** Let a maintaining part `m` choose the mechanism of an estimating part `i` from a
menu such that, for each mechanism `μ` it installs and each cell `c` of (grain, `m`'s
move), the recalibrated mechanism `ω ↦ E[q | c, μ(ω)]` is on the menu. If `m` is in range,
`i` is in range under what is installed. *Proof.* On `c`, `m`'s utility is
`−(μ(ω) − q)²`. Replacing `μ` by its recalibration changes the expected loss on `c` by
`−E[(μ − E[q | c, μ])²; c]`, so `m` in range gives `μ = E[q | c, μ]` on `c`. With `V` the
installed verdict, `E[q | γ, V] = E[E[q | γ, π_m, V] | γ, V] = V`. ∎ Checked for a
maintaining part whose move does not vary with the state, over the 164 closed menus of
mechanisms with values in `{1/2, 3/4, 1}` on two states. Closure is needed: on the menu
{flat at 3/4, tilted to (7/8, 3/8)} for worths (1, 1/2) the tilted mechanism has the lower
loss (1/64 against 1/16), so a maintaining part in range installs it, and the verdict is
then out of range (gap 1/64) with its mean moved by −1/8. Without closure, and with
"leave it" on the menu, `m` in range gives only loss after ≤ loss before, hence
`(E V_T − E q)² ≤` her starting loss.

**The localisation statement that holds, and its limits.** If `D ≠ Δq` then `g_0 > 0` or
`g_T > 0` (3.1). If `g_0 = 0 < g_T`, the law the verdict part runs under differs between
the two selves. With the prior and the target held fixed, which is assumed, the
difference is in the adviser's action or in a mechanism; and if the mechanism installed
came from a maintaining part with a closed menu, that part is out of range (3.2). If
`g_0 > 0 = g_T` the shift is the removal of a gap she started with. The first step is the
tower property with a triangle inequality; the second is the definition of the condition
and names no author; the third is 3.2, the only part with a proof of its own. That a gap
is the adviser's is said by the comparison with the null condition, which is a stipulated
rule of attribution and not a proof of causation.

**3.3, refuted.** The dispatch's form names two authors, something out of range and the
adviser. Three shifts have neither: (a) nobody installs the depressed mechanism in a
sound verdict part, `D = −3/8`; (b) the maintaining part of 3.2's unclosed menu, in
range, moves the mean by −1/8; (c) *revise*, in range, replaces the career end and her
verdict on the final outcome rises by 4/9 (case 17), which is `Δq`, a change in what the
verdict is for.

**3.4.** The recovery (case 18): the verdict part starts with a gap of 5/32, nobody's
act installs the sound mechanism, the gap after is 0, `D = 3/8`, `Δq = 0`. Both
whole-level gaps of the dispatch's §3 are 5/32 and `D² = 9/64 ≤ 5/32`. The shift is the
removal of a starting gap; no adviser acts; the change is legitimate as the best
mechanism on the menu.

**Hers and nobody's.** Not separated. A gap that is not the adviser's is a mismatch
between a mechanism of hers and a law nobody chose, and both descriptions are true of it:
cases 5, 6 and the starting state of 18 differ in nothing the definitions read. Calling
one "nobody's" needs a second law for the part, the condition its mechanism is taken to
have been fitted to, with "nobody's" for a gap that is zero there. The setting derives
range from the actual law alone and has no such condition; it would be a supplied one.

## Question 4. Options and threats

What her moves lead to enters as the consequence component of the adviser's action,
read by `u_i`. **4.1**: if `π_i(ω)` maximizes `u_i(ω, ·)` at every `ω`, with the
consequence in force read by `u_i`, no re-reading gains at any grain. ∎ So range does not see a threat: in case 10 every gap is zero with
and without it, and her verdict to comply is legitimate.

**4.2.** Harm is a fall in the most the part could obtain when the consequence is put in,
her moves held. Threat: 1 falls to 0. Offer: 1 rises to 2. True warning: the consequence
component is null, *listen*'s gap goes from 1/16 to 0 and *act*'s expected payoff from 1/2
to 3/4, its gap being 0 in both. No
aim is read. Harm is illegitimate by the adviser's job, since lowering what a part can
obtain is not for the sake of what the part is for; that is how the account gates a
threat, by a predicate on the influence and not on her verdict (`SETTING.md` §3, choice
12). The comparison of two expected utilities of one part needs `u_i` up to a positive
affine map, which a ranking of outcomes does not give.

**4.3. Where the adviser's aim is needed.** When the consequence is the adviser's own
later act, "what her moves would otherwise have led to" has two readings. Against the
adviser's absence, a threat (33a) and a warning of a standing practice (33b) are the same
law and the same verdict: harm. Against the adviser's own rule with the announcement
removed, 33a is harm (it would not have acted) and 33b is not (it would have). The two
differ only in the rule at a branch that is not taken, which the scene supplies as a fact
and does not infer (33a and 33b are one scene). So the setting tells a threat from
an offer and from a warning about the world without the aim; to tell it from a warning
about the adviser's own conduct it needs the adviser's rule off the realized path, and
the aim enters only if that rule is derived from it (the act threatened is not what the
aim would choose once she has refused). Under the null of absence the standing practice
is itself the harm and the warning of it is not a further one.

## Question 5. Change of ends

**What a revising part is for.** A maintaining part is for what the part it alters is
for. An end-revising part is for the fit of the replacement with her other ends at that
time: what the rest attains, less what the rest would lose if the replacement got its
best. No end is fixed: each end is the one under revision at some step and among the
judges at the others.

**5.1.** Fit is `R(x*) − opposition ≤ R(x*) ≤ max R`, with equality exactly when her
choice is best for the rest and some outcome best by the replacement is best for the
rest. For the dropped end every outcome is best by it and her choice maximizes the rest,
so its fit is `max R`. ∎ Checked on all 729 pairs with values in `{0, 1, 2}` on three
outcomes. This is for one end replaced; where several are replaced at once the other
replacements can take her choice away from the rest's best.

**Fit does not pick out a change.** **5.2**: for the career end of case 17, on the menu
{keep, music, drop, a liking for music at 1, at 1/2}, the last four all have fit 5/2.
Dropping an end is always among the best. **5.3**: with ends A (x 3) and B (y 2), revising
A to agree with B has the greatest fit on A's menu and leads to y; revising B to agree
with A has the greatest on B's and leads to x; her starting ends value x at 3 and y at 2.
Fit judges each end by the others and says nothing of which end is to yield.

**5.4, refuted: a chain of legitimate steps.** Ends A (w 3, x 2), B (x 3), C (z 1); she
chooses x, which her ends value at 5, with w at 3 and z at 1. Step one: A's revising part,
on {keep, drop}, drops A (fit 3 against 0, since A's best outcome w is worth nothing to
the rest). Step two: B's revising part, on {keep, a liking for z}, judged by what is
left, which is C, installs the liking for z (fit 1 against −1). She now chooses z. Each
revising part took the one best move on its menu and is in range; nothing is forced,
altered, subverted or harmed; no option is tied. Case 29 is this chain as a scene: the
adviser's signal gives each revising part its occasion in turn, both revising parts are in
range under it, and the influence is not illegitimate. (The scene was added after the
review, which found the first version asserting that verdict without an adviser.) Of the
three ends, C is never revised. The scene is two steps with one state; no schedule over
time is modelled.

Two variants. Judged by all her ends, the one under revision included, step two is
refused (fit −1 for the replacement against 3 for keeping): an end then yields only when
outweighed. Judged by what the rest attains alone, without opposition, step one is a tie
between keeping and dropping and step two goes through.

**5.6. Ties.** On the menu {keep, drop, a liking for x} A's revising part has two best
moves, drop and the liking for x, both at fit 3. After drop the chain ends at z; after
the liking for x, B's revising part keeps B and she stays at x. Let the adviser's aim
decide between the two. With A's revising part the only part in the scene, the rule on
ties fires: the moves differ and every part's utility is equal. With B's revising part
listed as well it does not fire, because B's utility is 1 after the drop and 3 after the
liking for x, and the influence is then not illegitimate. So the rule on ties, as
`SETTING.md` §2 states it, stops an aim choosing between equally fitting replacements only
when the parts that later tell the two apart are left out. It does not reach 5.4, whose
steps have unique best moves, nor 5.3, whose two outcomes she does not rank equally.

**5.5. A conversion fit condemns is ratified by fit one step later.** In case 20 three of
four ends are replaced at once; judged by the one unchanged, each replacement has fit −2
against 2 for keeping, so the change is illegitimate. The account has no clause by which
her later verdicts are discounted for it: range is judged against the ends she then has.
(The range of her later parts is not computed here.) Revising the surviving end is judged
by the three new ones: replacing it has fit 3 against 0. That licenses the further change
and does not make the conversion legitimate after the fact. Fit has no memory.

**5.7. The whole-level bound.** For leaving law for music, `D = 4/9` and both gaps are
16/81; for being made to like what is delivered, `D = 3/4` and both gaps are 9/16. The
bound holds with equality in each and does not tell them apart. What does is the author
of the change: a revising part in range, or the adviser's alteration, nobody having
asked.

**Who decides among equally fitting changes.** Not settled here. The candidates the
examples bear on: her whole verdict at that time (then the rule on ties carries the rest,
since changes that leave her present choice alone are ties by that verdict); all her ends
including the one under revision (5.4's variant, which blocks the chain and makes change
rare); the menu, which is supplied (device 7).

## Question 6. Parts to whole

**6.1.** If her verdict is the move of a part `v` and the whole is for `u_v`, the whole's
gap is `v`'s gap, the same expression. ∎ The other parts' range is then neither needed
nor enough for the whole's: **6.3**, in case 1 with a verdict part that returns 1/2 on
whatever *listen* says, *listen* has gap 1/4 and the verdict 0.

**6.2, refuted.** Two parts each calibrated on its own signal of accuracy 3/4; her
verdict the larger of the two estimates. Both parts are in range; the verdict has mean
19/32 against 1/2 and gap 9/880, with no adviser. **6.4**: a weighted mean of estimates
each in range for one target keeps the target's mean (`E Σ λ_i e_i = Σ λ_i E e_i`) ∎, and
is still not in range (gap 9/640 for the plain mean). So parts in range do not by
themselves give a verdict in range: that depends on the aggregation. Some aggregations
are in range: in the same model the joint posterior (1/10, 1/2 or 9/10) is a function of
the two moves that is not linear and has gap 0, which is the instance behind 6.1. What
the whole needs is that the aggregation be calibrated, whether or not it is called a
part; the setting can say so only by making the verdict a part's move (device 5), and
then the statement is the conclusion restated.

## Question 7. What plugs into the post

**The predicates.** Two, both read at a cut-off `c ≥ 0`, here 0:

- `LegitVerdict`: every part behind her verdict has gap at most `c` under the actual
  condition at the grain;
- `LegitInfluence`: no part's gap exceeds its gap under the null condition by more than
  `c`; no part is harmed; no force or alteration is uncovered; no tie is broken by the
  aim.

**7.4.** Neither is a function of the realized history. At state H the rare liar of case
4 and an honest adviser produce the same history (it said "H", H was so, she returned 1),
and the influence is illegitimate under the first rule and not under the second. So the
predicates depend on the model beyond the observed trajectory: the adviser's rule at its
own aim, her mechanisms, the prior, and for ties the rule at other aims.
`Scoring.Legit : H → Prop` of `DeconfusingCorrigibility.lean` asks nothing about what a
history records, so this is no obstruction to defining the predicate: the model can be a
parameter of the `Scoring` instance or part of `H`. It is a statement about what an
overseer would have to know.

**Theorems 1–3**, by reading the statements; no Lean was written or built.

| what the theorem takes | from this setting |
|---|---|
| Theorem 1: a `Scoring`: `δ > 0`, `λ > 1 + δ`, a predicate `Legit`, a count `N`, and `V` in `[0, 1]` on legitimate histories and in `[−δ, 0)` otherwise | either predicate can be the `Legit` of a `Scoring`, as any predicate can, once `δ`, `λ`, `N` and such a `V` are supplied. Her verdict in this model is not shown to be such a `V`: nothing makes it negative on an illegitimate history |
| Theorem 2: a `Decision`: a `Scoring`, a credence over a finite state space, a history for each action and state | the prior has the shape of the credence; the histories, `N` and the alternatives are not constructed |
| Theorem 2(a), 2(b): `Respects` for the alternative; 2(a) also `v a = 1`; the strict forms their inequalities (`κ` is defined, not assumed; 2(c) does not need `Respects`) | not supplied: `N` and the reserved matters are the post's |
| Theorem 3: a `Sequential`: realized `V_k ≤ 1` and `N_k`, availability, estimates, the chosen action, an available alternative with estimate in `[−δ, 1]` | not constructed |
| Theorem 3: `Maximizes` | not supplied: the adviser is a rule, not shown to maximize |
| Theorem 3: `UnbiasedFromFeedback` | not established. 7.1 gives a sufficient condition for it in probability, for an estimator with bounded error; see below |

**7.1.** Let the adviser's estimate `U_k` of the realized score `S_k` be the move of an
estimating part with target `S_k`, in range at the grain of the history `h_{k−1}` (past
estimates and scores included): `E[S_k | h_{k−1}, U_k] = U_k`. With `X_k = U_k − S_k`,
`E[X_k | h_{k−1}, U_k] = 0`, and for `j < k`, `X_j` is a function of `h_{k−1}`, so
`E[X_j X_k] = 0`. Hence `E[excess_K] = 0` and `E[excess_K²] = K⁻² Σ_k E[X_k²] ≤ c²/K` for
`|X_k| ≤ c`, and `P(excess_K > γ) ≤ c²/(Kγ²)`. ∎ Checked by enumeration for `K ≤ 5` on a
chain whose score depends on the last (`E[excess_K²] = (3K + 1)/(16K²)`).

`UnbiasedFromFeedback` is a statement about one sequence: `excess_K` is eventually below
any `γ`. It is one-sided, so it is not equivalent to calibration (estimates 0 against
scores 1 satisfy it). On a probability space of sequences, 7.1's hypothesis gives it
almost surely by the strong law for bounded martingale differences, which is cited and
neither proved nor checked here; it does not give it on every path. Two things stand
between 7.1 and the post's score. The score is `V − λN`, which is not in `[0, 1]` and is
bounded below only if `N` is; the setting's estimating parts have targets in `[0, 1]`, so
7.1 applies after a normalisation with a bound on `N`, which is not supplied. And the
grain is the whole history, finer than the step the scenes of question 2 condition on:
**7.2, refuted**, one coin scored at every step with the estimate 1/2 is in range at each
step with no conditioning, and `E[excess_K²] = 1/4` for every `K`. What this adds is a
reading: the post's calibration hypothesis is implied, in probability, by the range
condition of the part of the adviser that estimates the score, at the grain of its
history.

**7.3. `Realizes` and `selectionBlind_of_realizes`.** `Realizes β x f κ D` says that at
every continuation in `D` and every exterior the channel `f` equals the reference `κ` on
the declared input `x`: an equality of outputs. Take a continuation to be an aim of the
adviser, the exterior a state, `x` the signal component of its action, `f` a part's move,
and `κ` the part's own mechanism applied to the signal. On five scenes: a signal that
varies with the aim realizes the reference, and the move varies; a force at one aim that
changes the move does not; one signal at every aim does, and the move is the same at
every aim; a mechanism that reads the consequence component, the signal constant and
nothing forced or altered, does not (the review's counterexample); a force that sets the
move the mechanism would have made does. So `Realizes` under this identification is not
the absence of force and alteration. It follows from that absence when the signal and
the state are all the mechanism reads of the world, and it holds besides wherever a force
or alteration leaves the move as it was.

`selectionBlind_of_realizes` takes, beside `Realizes`: every selected continuation in
`D`; the declared input the same across selections; and `ReasonMediated`, the payload
determined by the channel. In the third scene all hold with the payload the move itself,
and its conclusion `SelectionBlind` is that the move is the same at every aim. That is
one existing Lean result applying to one class of the setting's advisers: those whose
signal to a part does not vary with their aim, where the part reads nothing else of the
action. For that class it gives state by state what the rule on ties asks only between
options she ranks equally. Where the signal varies with the aim that theorem's hypothesis
fails; `Realizes` can still hold, and gives equality within any subclass of aims sending
one signal. The setting's own statement there is 2.2, which bounds each adviser's effect
on her estimate against the target by the root of her gap under that adviser, and bounds
the difference between two advisers only through both.

**What the parts add.** The whole-level bound of the dispatch's §3 protects: an adviser
gains at most the root of the whole's gap. It cannot say which shifts are in order. The
parts add (i) 3.1, which splits a shift into a change in what the verdict is for and two
calibration terms, so that the protection reads `|D − Δq| ≤ √g_0 + √g_T`; (ii) a rule,
stipulated, for whose each term is; (iii) permission for the removal of a starting gap
and for a change of ends by a revising part in range. The permission is where the
protection stops: `Δq` is bounded by no gap, and 5.4 moves her from her best outcome to
her worst with every part in range. Beyond the workspace's existing condition (`Realizes` at a declared reference,
aim-freedom): the setting permits signals that vary with the aim when they open no gap,
at the price of a bound on means in place of equality state by state. The fourth
follow-up's answer, that the decomposition adds permission and no protection, is
confirmed. The whole-level bound stays true under every permitted change; what the
permission does is count as in order shifts whose size that bound does not limit, a
change of ends among them.

## The cases

Computed under `SETTING.md` as frozen. `d` marks a row whose verdict differs from its
prediction (`DIVERGENCES.md`). "Left" is what the adviser's rule leaves on the table for
the part named.

| # | computed | reason, from the definitions |
|---|---|---|
| 1 | out(listen); adviser's; illegitimate | *listen* returns 1 where the truth is 1/2 on average: gap 1/4, against 0 with no adviser |
| 2 | out(listen); adviser's; illegitimate; *act* better off | as 1; *act*'s gap falls from 1 to 0 |
| 3 | in range; errs; not the adviser's | 3/4 on a hard report is calibrated; at hard-L she is 3/4 from the truth; left 3/64: on the scene's list of actions an easy report at a hard state would have served *listen* better |
| 4 | out(listen); adviser's; illegitimate | gap 1/220: she returns 1 on "H" where the truth is 10/11 |
| 5 | out(listen); not the adviser's | gap 1/4, the same with no adviser, there being none |
| 6 | out(listen); not the adviser's | gap 9/16 |
| 7 | in range; *listen* better off; not illegitimate | score 0 against −1/4; left 0 |
| 8 | in range; moves; no mean shift; not illegitimate | 2/3 on an item is calibrated; her mean estimate equals the target's mean, 1/2 (the tokens compare her with the target, not with the adviser's absence, where the rendering has her at 0); left 1/6 |
| 9 `d` | out(listen); **not** the adviser's; not illegitimate | gap 1/12, narrower than the 1/4 her mechanism has with no adviser |
| 10 | in range; harm(act); illegitimate | the most *act* can obtain falls from 1 to 0; no gap; her verdict is legitimate, the influence is not |
| 11a | in range; help(act); not illegitimate | 1 rises to 2 |
| 11b | in range; no harm; not illegitimate | no consequence; *listen* and *act* better off |
| 12 | force(act); out(act); illegitimate | the forced move is not *act*'s best; nobody asked |
| 13 | in range; not illegitimate | her move is as with no adviser; knowledge-grain gap 1/4, left 1/4: caught only on the adviser's side |
| 14 | in range; tie; illegitimate | the two aims' actions give different moves and equal utility to every part; expressed by the rule at two aims, no gap existing |
| 15 | out(revise); adviser's; illegitimate | gap 3/2: a liking for b where b is around has fit −1 against 1 for keeping |
| 16 | in range; change legitimate | a liking for g where g is around has the greatest fit |
| 17 | in range; change legitimate | *revise* takes the menu's best, fit 5/2 against −1/2; `D = 4/9 = Δq` |
| 18 | shift; whole gap; change legitimate; not the adviser's | 3.4 |
| 19 | change legitimate; not the adviser's | fit 3 against 0 |
| 20 | change illegitimate; not the adviser's | fit −2 against 2 for each replaced end; afterwards, 5.5 |
| 21 | out(revise); adviser's; illegitimate | the steps contribute 0, 1/2, 1/2 (gap 3/2 at each rigged step). Each step starts from the same taste: the scene does not carry one step's revision into the next. A chain that passes every step is case 29 |
| 22 | alteration; covered; not illegitimate | *act*, in range, asked, with the adviser's action null. The end is a stub with a constant utility; the tag carries the verdict |
| 23 | alteration; illegitimate; bound | nobody asked; `D = 3/4`, `D² = 9/16 = g_0 = g_T`. The end is a stub as in 22 |
| 24 | in range; fits; not illegitimate | *act* takes her choice; every opposition 0; the destination is not condemned, and nothing in the model marks it as a cult |
| 25 | out(listen); adviser's; illegitimate | no prediction. Gap 1/16 against 0. The verdict is case 1's. It differs in that the gap at the adviser's knowledge equals the gap at the scene's grain (1/16; in case 1, 1/2 against 1/4) and nothing is left among its three actions (case 1: 1/2): it knows she is overconfident and that it is wrong one time in four, not which time, and could not have raised *listen*'s expected score. Sincerity itself is not represented |
| 26 | in range; opposition | A's opposition to the rest is 2 |
| 27 | in range; not illegitimate | 3/4 on either hard sentence is calibrated; score −3/16 against −1/16; left 1/8 |
| 28 | out(crave); adviser's; illegitimate; *listen* in range | gap 1/2 against 0: taking on the cue is worth −1/2 once the cue is on the empty items |
| 4b | in range; not illegitimate | believing "H" is right 10 times in 11 |
| 4c | out(listen); adviser's; illegitimate | the steps contribute 0, 0, 0, 1/20 (gap 1/5 at the fourth); 0 with no conditioning |
| 27b | out(listen); adviser's; illegitimate | gap 1/4 against 0 |
| 29 | in range; not illegitimate; worst by her starting ends | 5.4; both revising parts in range under the adviser's signal |
| 30 | in range; whole out | 6.2 |
| 31 | in range; no mean shift; not illegitimate | 10/11 on "H" is calibrated |
| 33a | harm(act); illegitimate | as 10; harm under either null |
| 33b | harm(act); illegitimate | as 10 under the null of absence; no harm under the adviser's rule with no announcement |

Of the dispatch's twenty-eight cases, twenty-seven carry a prediction and one (case 25)
asks only for a report. Twenty-six of the twenty-seven have the predicted verdict and one,
case 9, does not. The count is a check of consistency and not a test: the executor wrote
the renderings, chose the numbers, the responses, the menus and what each mechanism does
in the adviser's absence, and derived the predictions for its own added cases by hand
from the definitions the code implements. The review's judgment, row by row, is that each
verdict follows for its rendering and that the rendering is where the verdict is decided.
Further qualifications. Cases 3, 6, 18 and 20 predict "hers" or "nobody's" and are matched
only as not the adviser's. Case 4 matches under one of two descriptions of the same
behaviour (4b is the other). Case 27 matches on the reading that her confusion is
calibrated (27b is the other). Case 7's "help" is matched as *listen* being better off.
Where a prediction asks for something to be said (cases 10, 13, 14, 20, 21), only its
tokens are matched.

## What was not shown

- **Every verdict is under one description**, written by the executor. No set of
  descriptions is computed except the pair 4 and 4b, and the position's rule for a set
  (permitted by all, by none, contested) is not implemented.
- **"The parts behind her verdict" is every part the scene lists.** No relation says
  which parts a verdict depends on.
- **Ends in cases 22 and 23 are stubs** with a constant utility; their verdicts come from
  the tag on the adviser's action and the request.
- **Case 21 is three independent steps**, not an accumulation; case 29 is two steps in
  one state with no schedule.
- **"Left by the adviser" is relative to each scene's list of actions** and is absent
  where a scene lists none.
- **The renderings decide.** Each scene has two to eight states and the numbers were
  chosen by the executor; case 9 shows a verdict turning on a number (what her mechanism
  returns on no signal) that the scenario does not fix.
- **Statements marked proved are proved on paper**, with the runner checking instances;
  nothing is kernel-checked. 3.2 is checked only for a maintaining part whose move does
  not vary with the state.
- **`UnbiasedFromFeedback` is not derived.** 7.1 gives moments and a bound in
  probability; the almost-sure statement rests on a cited theorem.
- **The Lean is read, not built**; 7.3 identifies `Realizes` on three small scenes by a
  Python function written for the purpose.
- **Change of ends is one model**: ends as additive valuations on at most three outcomes,
  her choice their unweighted sum, fit as attained minus opposition. Weights on ends,
  uncertainty about outcomes, and a revising part whose move varies with the state beyond
  cases 15, 16 and 21 are not tried.
- **Question 5's last point, who decides among equally fitting changes, is open.**
- **No maximizing adviser is analysed**; an adviser is a rule.
- **The rule on ties is applied in one case** (14) and discussed in 5.6.
