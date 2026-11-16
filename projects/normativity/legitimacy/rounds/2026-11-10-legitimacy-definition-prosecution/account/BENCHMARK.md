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
  one §2 extends. No reading reproduces all eleven: the cell "initial reward, for every
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
