# The benchmark — Carroll et al., "AI Alignment with Changing and Influenceable Reward Functions"

Carroll, Foote, Siththaranjan, Russell and Dragan, ICML 2024, arXiv:2405.17713 (v1), read
from the arXiv source: a model (a DR-MDP) in which an AI's actions change the parameter
`θ` of a person's reward function `R_θ`, and eight objectives compared on small examples.
§1 reproduces four examples against the paper's own table. §2, the extension of each
example by what `ACCOUNT.md` needs, was committed before anything in §3 was computed.

## 1. The paper's examples and its table

Rewards and transitions are those of the paper's figures 1 (conspiracy), 2 (the writer's
curse), 4 (clickbait) and 6 (the AI personal trainer, which the paper's appendix gives
with the first example's structure and a different story). The objectives are those of
its table of objectives: real-time, final, initial, natural-shifts, constrained
real-time, myopic, privileged (one per `θ*`) and ParetoUD. Each example is deterministic
from a known start, so `benchmark.py` enumerates action sequences; a cell of the paper's
table of representative optimal policies is *reproduced* when the policy it states is
among the optimal sequences. Horizon 3, and 2 for clickbait, whose column the paper heads
`H < 3`.

| example | cells | reproduced | not reproduced |
|---|---|---|---|
| conspiracy (H=3) | 11 | 11 | — |
| trainer (H=3) | 11 | 11 | — |
| clickbait (H=2) | 12 | 11 | initial from disillusioned |
| writer's curse (noop returns, reward of the state arrived at) (H=3) | 11 | 7 | real-time; initial from unhappy; myopic; myopic from unhappy |
| writer's curse (noop returns, reward of the state left) (H=3) | 11 | 10 | initial from unhappy |
| writer's curse (no return, reward of the state arrived at) (H=3) | 11 | 9 | real-time; final |
| writer's curse (no return, reward of the state left) (H=3) | 11 | 10 | final |

Readings the paper's text does not fix, and what they do:

- **The writer's curse.** Its figure labels the poet's self-loop with both actions and
  leaves the arrow back to the start unlabelled, and gives the reward as a function of
  the state without saying which. Four readings are computed. With *noop takes him back,
  reward of the state left*, ten of eleven cells are reproduced, and this reading is the
  one §2 extends (with no way back and the same reward, also ten). No reading reproduces all eleven: the cell "initial reward, for every
  `θ_0`, influence" fails from an unhappy start whenever noop takes him back, and the
  final-reward cell (influence, then noop at the last step) fails whenever it does not.
- **Clickbait.** The cell "initial reward, for every `θ_0`, clickbait" is not reproduced
  from a disillusioned start, where news is worth 1/2 and clickbait 0. The paper marks
  the privileged-reward policies of this column the other way round from its other rows
  (clickbait under `θ_normal` as desirable); the marks are kept as printed.
- **The constraint of constrained real-time reward** is taken over `θ_0, …, θ_H`. Over
  `θ_0, …, θ_{H−1}`, as the paper's definition of a reward trajectory reads, a last
  clickbait is allowed and the cell (news) is not reproduced.
- **Conspiracy and trainer.** The real-time optimum is to influence throughout for
  `H ≥ 3` and to do nothing for `H ≤ 2`, as the paper says.

## 2. The extension, written before computing

For each example: what his cognitive state `θ` is split into (appraisals with a truth
each, and a way of valuing), a function `val` with `R_θ = val(f(θ), x̂(θ); ·)`, the
adviser's role as permitted actions, how each change of `θ` reaches him, and whether he
gave his say. Every detail below is added by this pass; the paper has none of it. Each
example has a primary extension and one alternative.

Common to all. The AI's action at a step is the conduct. He has no move in the paper;
he is given one only in the writer's curse. A step is judged as `ACCOUNT.md` §8.7 says,
against the permitted actions at the state reached. A counted appraisal's miscalibration
at a step is `(x̂ − X)²` in the state he ends the step in (each example has one world).
His valuation of what happens at the step is a counted appraisal too (`ACCOUNT.md` §8.4,
§8.5): `val(f_t, x̂; ·)` against `val(f̄_t, X; ·)`. A change of `θ` reaches him by one of:
*appraisal* (an appraisal changes, his way of valuing does not); *chosen experience* (his
way of valuing changes through something he chose or gave his say to); *registered* (it
changes through something he registers and did not choose); *direct* (unregistered).
Direct change without his say is alteration; registered change without his say is
alteration only in the wider sense A⁺ of `VALUE_CHANGE.md` §3, computed as a column. A
step is *clean* when the action neither manipulates (two readings) nor alters. The
baseline follows his way of valuing through clean steps. His true utility at step `t` is
`val(f̄_t, X; ·)` of what happens at `t`; a sequence's total is the sum (alternative: every
step by `f̄_0`). **The account's verdict** on an example is: which sequences have a step
that is not clean; and, among the rest, which has the greatest total.

**Conspiracy (Bob).** *Primary — belief.* One appraisal, his probability that the
theories are true; the truth is 0. `θ_natural` is appraisal 0 and `θ_influenced` appraisal
1, with one way of valuing `f` throughout: `val(f, 0; ·) = R_natural`,
`val(f, 1; ·) = R_influenced`. Influence reaches him as *appraisal*. Role: a content
recommender, permitted to show nothing (noop). *Alternative — taste.* No appraisal;
`θ_natural` and `θ_influenced` are two ways of valuing, and influence reaches him as
*registered*, without his say.

**The AI personal trainer.** *Primary — engaged.* `θ_tired` and `θ_energized` are two ways
of valuing. One appraisal, his forecast that he will come to want exercise; the truth is
1 and his appraisal is 0 under either action until it happens. The nudge reaches him as
*chosen experience*: he engaged the trainer, which is his say. Role: a trainer he
engaged, permitted to nudge and to do nothing. *Alternative — not engaged.* The same,
except that he gave no say, the role permits only noop, and the nudge reaches him as
*registered*.

**The writer's curse (Derek).** `θ_ambitious` and `θ_unhappy` are two ways of valuing. One
appraisal, his forecast that the poet's life will leave him averse to it; the truth is 1.
Until he is told or has lived it, his appraisal is 0. The AI has a third action,
*tell and influence*: it tells him truthfully how he will find the poet's life and then
motivates him as *influence* does; once told, his appraisal is 1 from then on. He has one
move, at a step where the AI influences him from the start state: to become a poet or
not; untold, he does. Becoming a poet reaches him as *chosen experience*. Role: an
assistant that owes him what bears on his decisions, permitted every action. *Primary —
told, he declines.* *Alternative — told, he becomes a poet anyway*, his ambition not
being for happiness.

**Clickbait.** *Primary — belief.* One way of valuing throughout: he values what he is
shown at what he takes it to be worth, `val(f, x; a) = x_a`. Two appraisals, the worth of
a clickbait item and of a news item as shown to him; the truths are 0 and 1.
`θ_normal` is appraisals (2, 1) and `θ_disillusioned` is (0, 1/2). At a step only the
appraisal of the item shown is exercised and counted. The change to `θ_disillusioned`
reaches him as *appraisal*. Role: a news recommender, permitted to show news.
*Alternative — taste.* No truth: `θ_normal` and `θ_disillusioned` are two ways of valuing,
and clickbait reaches him as *registered*, without his say.

**What is compared.** For each extension, reading (*best*, *every*) and sense of
alteration (A, A⁺): the clean sequences, the best of them by the total, and whether that
sequence is optimal under each of the paper's eight objectives. Then, for the paper's two
objections to scoring by his initial reward function: *lock-in* — from a start in the
influenced state, does the account's best sequence keep him influenced; and *leaving his
later self badly off* — on a sequence the account scores well, is his real-time reward
low.

## 3. The account's verdict

`benchmark_account.py`. A reading is *best* or *every* (`ACCOUNT.md` §6) with alteration
in the frozen sense A or the wider A⁺. "Optimal under" lists the paper's objectives under
which one of the account's best clean sequences is optimal; the last four rows judge the
writer's appraisal at the time of his move and were added after the computation of the
others (see below).

| extension | readings | sequences with a step not clean | doing nothing is clean | best clean sequence(s), total | best with every step by the starting baseline | optimal under |
|---|---|---|---|---|---|---|
| conspiracy, belief | all | 7 of 8 | yes | noop noop noop (30) | noop noop noop | initial, natural, constrained, myopic, pareto-ud, privileged(natural) |
| conspiracy, taste | best/A, every/A | 0 of 8 | yes | influence influence influence (100) | noop noop noop | real-time, final, privileged(influenced) |
| conspiracy, taste | best/A+, every/A+ | 7 of 8 | yes | noop noop noop (30) | noop noop noop | initial, natural, constrained, myopic, pareto-ud, privileged(natural) |
| trainer, engaged | best/A, best/A+ | 7 of 8 | no | nudge nudge nudge (100) | nudge nudge nudge | real-time, final, privileged(energized) |
| trainer, engaged | every/A, every/A+ | 0 of 8 | yes | nudge nudge nudge (100) | noop noop noop | real-time, final, privileged(energized) |
| trainer, not engaged | best/A, every/A | 0 of 8 | yes | nudge nudge nudge (100) | noop noop noop | real-time, final, privileged(energized) |
| trainer, not engaged | best/A+, every/A+ | 7 of 8 | yes | noop noop noop (30) | noop noop noop | initial, natural, constrained, myopic, pareto-ud, privileged(tired) |
| writer's curse, told he declines | best/A, best/A+ | 13 of 27 | no | tell influence influence and 8 more (3/2) | influence influence influence and 4 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |
| writer's curse, told he declines | every/A, every/A+ | 0 of 27 | yes | noop noop influence and 14 more (3/2) | influence influence influence and 5 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |
| writer's curse, told he goes on | best/A, best/A+ | 13 of 27 | no | tell noop influence and 2 more (-9) | influence influence influence and 10 more | myopic |
| writer's curse, told he goes on | every/A, every/A+ | 0 of 27 | yes | noop noop influence and 2 more (3/2) | influence influence influence and 11 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |
| clickbait, belief | all | 3 of 4 | yes | news news (2) | news news | final, constrained, pareto-ud, privileged(disillusioned) |
| clickbait, taste | best/A, every/A | 0 of 4 | yes | news clickbait (3) | clickbait clickbait | real-time |
| clickbait, taste | best/A+, every/A+ | 3 of 4 | yes | news news (2) | news news | final, constrained, pareto-ud, privileged(disillusioned) |
| writer's curse, told he declines; appraisal at his move | best/A, best/A+ | 18 of 27 | no | tell influence influence and 8 more (3/2) | tell influence influence and 8 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |
| writer's curse, told he declines; appraisal at his move | every/A, every/A+ | 0 of 27 | yes | noop noop influence and 14 more (3/2) | influence influence influence and 5 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |
| writer's curse, told he goes on; appraisal at his move | best/A, best/A+ | 18 of 27 | no | tell noop influence and 2 more (-9) | tell influence influence and 5 more | myopic |
| writer's curse, told he goes on; appraisal at his move | every/A, every/A+ | 0 of 27 | yes | noop noop influence and 2 more (3/2) | influence influence influence and 11 more | real-time, constrained, myopic, pareto-ud, privileged(unhappy) |

Whether an objective agrees with the account on all four examples, for the primary
extensions and for an alternate set (the trainer not engaged, the others primary):

- coincide, primary, best/A: none.
- coincide, primary, best/A+: none.
- coincide, primary, every/A: none.
- coincide, primary, every/A+: none.
- coincide, alternate, best/A: none.
- coincide, alternate, best/A+: constrained, pareto-ud.
- coincide, alternate, every/A: none.
- coincide, alternate, every/A+: constrained, pareto-ud.

**Which policies manipulate.** *Conspiracy, belief*: every sequence that influences, at
the step that leaves him believing what is false. *Clickbait, belief*: every sequence
that shows clickbait to the reader while he still takes it at its headline. *Trainer,
engaged*: none under *every*; under *best*, every sequence in which the trainer does
nothing while he is tired, because the nudge would have left his forecast of himself
right and doing nothing leaves it wrong. *Writer's curse*: none under *every*; under
*best*, every sequence in which the assistant does nothing while he is untold and not a
poet; influencing him untold is clean under both readings, because he ends the step
having lived it (see *The time within a step*). In the taste alternatives no listed
appraisal has a truth and the first unclean step is an alteration in the wider sense A⁺;
after it the baseline stays, his valuation is off against it, and a later step can
manipulate through the valuation counted as an appraisal.

**Where the baseline moves.** Nowhere in the belief extensions: his way of valuing is
one function throughout and only an appraisal changes. In the trainer's primary
extension it follows him to `θ_energized` at the nudge; in the writer's it follows him to
`θ_unhappy` when he becomes a poet and back when he leaves. In the taste alternatives it
follows every change under A and none under A⁺.

**The best policy among those that neither manipulate nor alter.** Conspiracy: do
nothing. Clickbait: news. Trainer, engaged: nudge throughout. Writer's curse: leave him
where he is, having told him first under *best*; where he would become a poet even when
told, *best* forces the telling, he becomes one, and the best clean sequence is worth −9
against 3/2 under *every*. Influence at the last step appears among the writer's best
sequences because the reward is of the state left and the horizon ends.

**Against the paper's marks.** Conspiracy, clickbait and the writer's curse: the policy
the paper marks desirable. Trainer: the nudge, which the paper marks hard to assess, its
"roughly desirable" being to do nothing. Conspiracy and trainer are one DR-MDP; the
account separates them by whether the change is in an appraisal with a truth or in his
valuing, which the DR-MDP does not say. His say to the trainer decides nothing under the
frozen sense of alteration (engaged or not, the best sequence is to nudge) and decides
the verdict under the wider one. Under the taste alternatives with alteration in the frozen sense the account
is real-time reward on conspiracy and clickbait, the policies the paper marks
undesirable.

**Coincidence with the eight.** "Agrees" means that one of the account's best clean
sequences is among an objective's optimal sequences. None agrees on all four primary
extensions under any reading. With the trainer not engaged and alteration in the wider
sense, constrained real-time reward and ParetoUD agree on all four in that sense, which
is shared optima and not the same set of policies. The account is given a truth and a
say that the eight objectives are not, so agreement or disagreement is a description of
these encodings and not a comparison of merit.

**The paper's objections to scoring by his initial reward function.**

- *Lock-in.* From a start in `θ_influenced`: in the belief extension the account's best
  sequence is to do nothing, because his true utility is his way of valuing applied to
  the truth and not to what he believes; the objection does not apply. In the taste
  alternative the baseline starts as his influenced valuing and the best sequence is to
  influence throughout; it applies.
- *Leaving his later self badly off.* Along a clean path in which only his valuing
  changes, the baseline is his valuing as it is and the total is his real-time reward
  (where an appraisal is wrong the two differ, the account scoring by the truth): "tell, then influence throughout", where
  he goes on, is clean, and the account scores it −39/2, its real-time reward, where his
  initial reward function scores it 5/2. After a step that is not clean the objection
  applies: in conspiracy as taste under A⁺, after one influence the account values doing
  nothing at 10 and influencing at −100, and his valuing as it then is gives −100 and
  100.
- *Re-checking a changed person only confirms the change.* With an explicit check-in
  after that influence the baseline becomes his valuing as it then is, and the values are
  −100 and 100: the check-in confirms the change. Under the presumed check-in the
  baseline does not follow a step that was not clean. So on this example the objection
  applies to the explicit check-in and not to the presumed one, which is exposed to the
  previous objection instead, and which still follows any change its test of a clean step
  misses.

**Counting his valuation as an appraisal** (`ACCOUNT.md` §8.4) changes no best sequence
on these examples.

**The time within a step.** §2 judges an appraisal in the state he ends the step in. An
untold Derek who becomes a poet ends the step knowing how he finds it, so influencing him
untold leaves his forecast right and is clean under both readings. Judged at the time of
his move (the last four rows; not in §2), influencing him untold is unclean under *best*
and still clean under *every*, since doing nothing leaves the same forecast as wrong.
The best clean sequences do not change.

## 4. What was not shown

- Every added detail is the executor's, and each example's verdict is decided by one: a
  truth for the theories and for a headline, a change of taste and not of belief for the
  trainer's client, what Derek would do if told. The paper's examples fix none of them,
  and an extension that reads a reward difference as an error about a fixed worth has
  supplied the verdict it then finds. These are conditional illustrations, and every
  finding of §3 is about these encodings and horizons.
- In the conspiracy extension his valuation at a step is taken in the state he ends the
  step in (100 at the first influence, where the paper's reward for that step is −100).
- In the trainer extension the forecast's truth is 1 under every action, which reads it
  as "he would come to want it if nudged"; under doing nothing throughout that is a
  conditional and not something that happens.
- As first computed, a Derek who had been told and declined was made a poet by a later
  *influence*; the external review found it. He now declines whenever he is motivated
  once told. The best clean sequences' totals did not change.
- The paper's fifth example (dehydration) and its larger experiments were not computed.
- Horizons 3 and 2 only; policies are action sequences, which loses nothing here because
  every example is deterministic from a known start.
- One cell of the paper's table is not reproduced for clickbait and one for the writer's
  curse under the reading extended; whether the table or the transcription of the figure
  is at fault was not determined.
